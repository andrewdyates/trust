// trust-convergence/dashboard_data.rs: Dashboard data preparation for visualization.
//
// Transforms convergence metrics and history into structured data suitable for
// rendering dashboards: summary cards, chart data, tables, and alerts.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::metrics::ConvergenceMetrics;
use crate::stagnation::count_trailing_equal;
use crate::visualization::FrontierSnapshot;

// ---------------------------------------------------------------------------
// Top-level dashboard data
// ---------------------------------------------------------------------------

/// Complete dashboard data payload, ready for rendering.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct DashboardData {
    /// High-level summary cards (KPIs).
    pub summary: Vec<SummaryCard>,
    /// Chart datasets for visualization.
    pub charts: Vec<ChartData>,
    /// Tabular data sections.
    pub tables: Vec<TableData>,
    /// Active alerts and warnings.
    pub alerts: Vec<Alert>,
}

/// Build a complete dashboard from metrics and frontier history.
#[must_use]
pub(crate) fn build_dashboard(metrics: &ConvergenceMetrics, history: &[FrontierSnapshot]) -> DashboardData {
    let summary = build_summary_cards(metrics);
    let charts = vec![
        build_convergence_chart(history),
        build_timing_chart(metrics),
        build_solver_pie_chart(metrics),
        build_cache_hit_chart(metrics),
    ];
    let tables = build_tables(metrics);
    let alerts = evaluate_alerts(metrics);

    DashboardData { summary, charts, tables, alerts }
}

// ---------------------------------------------------------------------------
// Summary cards
// ---------------------------------------------------------------------------

/// A single KPI card for the dashboard header.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct SummaryCard {
    /// Card title (e.g., "Total Iterations").
    pub title: String,
    /// Display value (e.g., "12").
    pub value: String,
    /// Trend arrow: "up", "down", "flat", or "none".
    pub trend_arrow: TrendArrow,
    /// Semantic color for the card.
    pub color: CardColor,
}

/// Direction of trend for a summary card.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum TrendArrow {
    Up,
    Down,
    Flat,
    None,
}

/// Semantic color for dashboard elements.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum CardColor {
    Green,
    Yellow,
    Red,
    Blue,
    Gray,
}

/// Build summary cards from convergence metrics.
#[must_use]
pub(crate) fn build_summary_cards(metrics: &ConvergenceMetrics) -> Vec<SummaryCard> {
    let mut cards = Vec::new();

    // Total iterations
    cards.push(SummaryCard {
        title: "Total Iterations".to_string(),
        value: metrics.iterations.to_string(),
        trend_arrow: TrendArrow::None,
        color: CardColor::Blue,
    });

    // Latest VCs proven
    let last_proven = metrics.vcs_proven_per_iteration.last().copied().unwrap_or(0);
    let prev_proven = metrics
        .vcs_proven_per_iteration
        .len()
        .checked_sub(2)
        .and_then(|i| metrics.vcs_proven_per_iteration.get(i))
        .copied();
    let (proven_arrow, proven_color) = match prev_proven {
        Some(prev) if last_proven > prev => (TrendArrow::Up, CardColor::Green),
        Some(prev) if last_proven < prev => (TrendArrow::Down, CardColor::Red),
        Some(_) => (TrendArrow::Flat, CardColor::Yellow),
        None => (TrendArrow::None, CardColor::Blue),
    };
    cards.push(SummaryCard {
        title: "VCs Proven (Latest)".to_string(),
        value: last_proven.to_string(),
        trend_arrow: proven_arrow,
        color: proven_color,
    });

    // Latest time per iteration
    let last_time = metrics.time_per_iteration.last().copied().unwrap_or(0);
    let prev_time = metrics
        .time_per_iteration
        .len()
        .checked_sub(2)
        .and_then(|i| metrics.time_per_iteration.get(i))
        .copied();
    let (time_arrow, time_color) = match prev_time {
        // For time, down is good (faster).
        Some(prev) if last_time < prev => (TrendArrow::Down, CardColor::Green),
        Some(prev) if last_time > prev => (TrendArrow::Up, CardColor::Red),
        Some(_) => (TrendArrow::Flat, CardColor::Yellow),
        None => (TrendArrow::None, CardColor::Blue),
    };
    cards.push(SummaryCard {
        title: "Iteration Time (ms)".to_string(),
        value: last_time.to_string(),
        trend_arrow: time_arrow,
        color: time_color,
    });

    // Cache hit rate
    let last_cache = metrics.cache_hit_rate_per_iteration.last().copied().unwrap_or(0.0);
    let cache_color = if last_cache >= 0.7 {
        CardColor::Green
    } else if last_cache >= 0.3 {
        CardColor::Yellow
    } else {
        CardColor::Red
    };
    cards.push(SummaryCard {
        title: "Cache Hit Rate".to_string(),
        value: format!("{:.0}%", last_cache * 100.0),
        trend_arrow: TrendArrow::None,
        color: cache_color,
    });

    // Strengthening proposals
    let total_proposals: u32 = metrics.strengthening_proposals_per_iteration.iter().sum();
    cards.push(SummaryCard {
        title: "Total Strengthening Proposals".to_string(),
        value: total_proposals.to_string(),
        trend_arrow: TrendArrow::None,
        color: if total_proposals > 0 { CardColor::Green } else { CardColor::Gray },
    });

    cards
}

// ---------------------------------------------------------------------------
// Chart data
// ---------------------------------------------------------------------------

/// Type of chart to render.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum ChartType {
    Line,
    Bar,
    Pie,
    Area,
}

/// A single data point in a chart.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct DataPoint {
    /// X-axis value (typically iteration number or label).
    pub x: f64,
    /// Y-axis value.
    pub y: f64,
    /// Optional label for this point.
    pub label: Option<String>,
}

/// Dataset for a chart visualization.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct ChartData {
    /// Chart title.
    pub title: String,
    /// Type of chart.
    pub chart_type: ChartType,
    /// Data points.
    pub data_points: Vec<DataPoint>,
    /// Axis labels.
    pub labels: ChartLabels,
    /// Series colors (CSS-compatible color strings).
    pub colors: Vec<String>,
}

/// Labels for chart axes and legend.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ChartLabels {
    pub x_axis: String,
    pub y_axis: String,
    pub legend: Vec<String>,
}

/// Build a convergence chart: VCs proven over time from frontier history.
#[must_use]
pub(crate) fn build_convergence_chart(history: &[FrontierSnapshot]) -> ChartData {
    let data_points: Vec<DataPoint> = history
        .iter()
        .map(|snap| DataPoint {
            x: snap.iteration as f64,
            y: snap.proved_count as f64,
            label: Some(format!("Iter {}", snap.iteration)),
        })
        .collect();

    ChartData {
        title: "VCs Proven Over Iterations".to_string(),
        chart_type: ChartType::Line,
        data_points,
        labels: ChartLabels {
            x_axis: "Iteration".to_string(),
            y_axis: "VCs Proven".to_string(),
            legend: vec!["Proved".to_string()],
        },
        colors: vec!["#4CAF50".to_string()],
    }
}

/// Build a timing chart: time per iteration from metrics.
#[must_use]
pub(crate) fn build_timing_chart(metrics: &ConvergenceMetrics) -> ChartData {
    let data_points: Vec<DataPoint> = metrics
        .time_per_iteration
        .iter()
        .enumerate()
        .map(|(i, &ms)| DataPoint {
            x: i as f64,
            y: ms as f64,
            label: Some(format!("Iter {i}")),
        })
        .collect();

    ChartData {
        title: "Time Per Iteration".to_string(),
        chart_type: ChartType::Bar,
        data_points,
        labels: ChartLabels {
            x_axis: "Iteration".to_string(),
            y_axis: "Time (ms)".to_string(),
            legend: vec!["Duration".to_string()],
        },
        colors: vec!["#2196F3".to_string()],
    }
}

/// Build a solver usage pie chart from cumulative solver times.
#[must_use]
pub(crate) fn build_solver_pie_chart(metrics: &ConvergenceMetrics) -> ChartData {
    let mut entries: Vec<(&String, &u64)> = metrics.solver_time_totals.iter().collect();
    entries.sort_by(|a, b| b.1.cmp(a.1));

    let colors = ["#4CAF50", "#2196F3", "#FF9800", "#F44336", "#9C27B0", "#00BCD4"];

    let data_points: Vec<DataPoint> = entries
        .iter()
        .enumerate()
        .map(|(i, (name, ms))| DataPoint {
            x: i as f64,
            y: **ms as f64,
            label: Some((*name).clone()),
        })
        .collect();

    let legend: Vec<String> = entries.iter().map(|(name, _)| (*name).clone()).collect();
    let chart_colors: Vec<String> = (0..entries.len())
        .map(|i| colors[i % colors.len()].to_string())
        .collect();

    ChartData {
        title: "Solver Time Distribution".to_string(),
        chart_type: ChartType::Pie,
        data_points,
        labels: ChartLabels {
            x_axis: "Solver".to_string(),
            y_axis: "Time (ms)".to_string(),
            legend,
        },
        colors: chart_colors,
    }
}

/// Build a cache hit rate chart over iterations.
#[must_use]
pub(crate) fn build_cache_hit_chart(metrics: &ConvergenceMetrics) -> ChartData {
    let data_points: Vec<DataPoint> = metrics
        .cache_hit_rate_per_iteration
        .iter()
        .enumerate()
        .map(|(i, &rate)| DataPoint {
            x: i as f64,
            y: rate * 100.0,
            label: Some(format!("Iter {i}")),
        })
        .collect();

    ChartData {
        title: "Cache Hit Rate Over Iterations".to_string(),
        chart_type: ChartType::Area,
        data_points,
        labels: ChartLabels {
            x_axis: "Iteration".to_string(),
            y_axis: "Hit Rate (%)".to_string(),
            legend: vec!["Cache Hit Rate".to_string()],
        },
        colors: vec!["#FF9800".to_string()],
    }
}

// ---------------------------------------------------------------------------
// Table data
// ---------------------------------------------------------------------------

/// Tabular data for the dashboard.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct TableData {
    /// Table title.
    pub title: String,
    /// Column headers.
    pub headers: Vec<String>,
    /// Row data (each row is a vector of cell strings).
    pub rows: Vec<Vec<String>>,
}

/// Build tabular views from metrics.
#[must_use]
pub(crate) fn build_tables(metrics: &ConvergenceMetrics) -> Vec<TableData> {
    let mut tables = Vec::new();

    // Solver performance table
    if !metrics.solver_time_totals.is_empty() {
        let mut solver_rows: Vec<(String, u64)> =
            metrics.solver_time_totals.iter().map(|(k, &v)| (k.clone(), v)).collect();
        solver_rows.sort_by(|a, b| b.1.cmp(&a.1));

        let total_solver_time: u64 = solver_rows.iter().map(|(_, v)| v).sum();

        tables.push(TableData {
            title: "Solver Performance".to_string(),
            headers: vec![
                "Solver".to_string(),
                "Total Time (ms)".to_string(),
                "Share (%)".to_string(),
            ],
            rows: solver_rows
                .iter()
                .map(|(name, ms)| {
                    let share = if total_solver_time > 0 {
                        (*ms as f64 / total_solver_time as f64) * 100.0
                    } else {
                        0.0
                    };
                    vec![name.clone(), ms.to_string(), format!("{share:.1}")]
                })
                .collect(),
        });
    }

    // VC kind failure table
    if !metrics.vc_kind_failure_totals.is_empty() {
        let mut failure_rows: Vec<(String, u32)> =
            metrics.vc_kind_failure_totals.iter().map(|(k, &v)| (k.clone(), v)).collect();
        failure_rows.sort_by(|a, b| b.1.cmp(&a.1));

        tables.push(TableData {
            title: "VC Kind Failures".to_string(),
            headers: vec!["VC Kind".to_string(), "Total Failures".to_string()],
            rows: failure_rows.iter().map(|(kind, count)| vec![kind.clone(), count.to_string()]).collect(),
        });
    }

    // Function retries table
    if !metrics.function_retry_totals.is_empty() {
        let mut retry_rows: Vec<(String, u32)> =
            metrics.function_retry_totals.iter().map(|(k, &v)| (k.clone(), v)).collect();
        retry_rows.sort_by(|a, b| b.1.cmp(&a.1));

        tables.push(TableData {
            title: "Function Retries".to_string(),
            headers: vec!["Function".to_string(), "Total Retries".to_string()],
            rows: retry_rows.iter().map(|(func, count)| vec![func.clone(), count.to_string()]).collect(),
        });
    }

    tables
}

// ---------------------------------------------------------------------------
// Alerts
// ---------------------------------------------------------------------------

/// Alert rule that triggers dashboard warnings.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum AlertRule {
    /// VCs proven per iteration has not increased for N consecutive iterations.
    StagnationDetected { consecutive_flat_iterations: u32 },
    /// VCs proven decreased compared to a previous iteration.
    RegressionDetected { from_iteration: u32, to_iteration: u32 },
    /// Total time exceeded a budget.
    BudgetExceeded { total_ms: u64, budget_ms: u64 },
}

/// Severity levels for alerts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) enum AlertSeverity {
    Info,
    Warning,
    Critical,
}

/// A triggered alert with context.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Alert {
    /// Which rule triggered this alert.
    pub rule: AlertRule,
    /// Human-readable message.
    pub message: String,
    /// Severity level.
    pub severity: AlertSeverity,
}

/// Default stagnation threshold (consecutive flat iterations).
const STAGNATION_THRESHOLD: u32 = 3;

/// Default time budget in milliseconds (10 minutes).
const DEFAULT_BUDGET_MS: u64 = 600_000;

/// Evaluate alert rules against current metrics.
#[must_use]
pub(crate) fn evaluate_alerts(metrics: &ConvergenceMetrics) -> Vec<Alert> {
    evaluate_alerts_with_budget(metrics, DEFAULT_BUDGET_MS)
}

/// Evaluate alerts with a custom time budget.
#[must_use]
pub(crate) fn evaluate_alerts_with_budget(metrics: &ConvergenceMetrics, budget_ms: u64) -> Vec<Alert> {
    let mut alerts = Vec::new();

    // Check for stagnation: consecutive iterations with same VCs proven.
    // tRust #163: uses consolidated stagnation primitive from stagnation module.
    let stagnation = count_trailing_equal(&metrics.vcs_proven_per_iteration);
    if stagnation >= STAGNATION_THRESHOLD {
        alerts.push(Alert {
            rule: AlertRule::StagnationDetected {
                consecutive_flat_iterations: stagnation,
            },
            message: format!(
                "Proving rate has been flat for {stagnation} consecutive iterations"
            ),
            severity: if stagnation >= 5 {
                AlertSeverity::Critical
            } else {
                AlertSeverity::Warning
            },
        });
    }

    // Check for regression: any iteration where VCs proven decreased.
    if let Some((from_iter, to_iter)) = detect_regression(&metrics.vcs_proven_per_iteration) {
        alerts.push(Alert {
            rule: AlertRule::RegressionDetected {
                from_iteration: from_iter,
                to_iteration: to_iter,
            },
            message: format!(
                "VCs proven decreased from iteration {from_iter} to iteration {to_iter}"
            ),
            severity: AlertSeverity::Warning,
        });
    }

    // Check time budget.
    let total_ms: u64 = metrics.time_per_iteration.iter().sum();
    if total_ms > budget_ms {
        alerts.push(Alert {
            rule: AlertRule::BudgetExceeded { total_ms, budget_ms },
            message: format!(
                "Total verification time ({total_ms}ms) exceeded budget ({budget_ms}ms)"
            ),
            severity: AlertSeverity::Critical,
        });
    }

    alerts
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

/// Find the first pair of consecutive iterations where VCs proven decreased.
/// Returns `(from_index, to_index)` as 0-based iteration indices.
fn detect_regression(vcs_proven: &[u32]) -> Option<(u32, u32)> {
    for window in vcs_proven.windows(2) {
        let (prev, curr) = (window[0], window[1]);
        if curr < prev {
            // Find the index from the position in the slice.
            let idx = vcs_proven.windows(2).position(|w| w[0] == prev && w[1] == curr)?;
            return Some((idx as u32, idx as u32 + 1));
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::fx::FxHashMap;

    use super::*;
    use crate::metrics::ConvergenceMetrics;
    use crate::visualization::FrontierSnapshot;

    fn make_metrics(
        vcs_proven: Vec<u32>,
        times: Vec<u64>,
        cache_rates: Vec<f64>,
    ) -> ConvergenceMetrics {
        ConvergenceMetrics {
            iterations: vcs_proven.len() as u32,
            time_per_iteration: times,
            vcs_proven_per_iteration: vcs_proven,
            strengthening_proposals_per_iteration: vec![0; 0],
            cache_hit_rate_per_iteration: cache_rates,
            solver_time_totals: FxHashMap::default(),
            vc_kind_failure_totals: FxHashMap::default(),
            function_retry_totals: FxHashMap::default(),
        }
    }

    fn make_metrics_full(
        vcs_proven: Vec<u32>,
        times: Vec<u64>,
        proposals: Vec<u32>,
        cache_rates: Vec<f64>,
        solvers: Vec<(&str, u64)>,
        vc_failures: Vec<(&str, u32)>,
        retries: Vec<(&str, u32)>,
    ) -> ConvergenceMetrics {
        ConvergenceMetrics {
            iterations: vcs_proven.len() as u32,
            time_per_iteration: times,
            vcs_proven_per_iteration: vcs_proven,
            strengthening_proposals_per_iteration: proposals,
            cache_hit_rate_per_iteration: cache_rates,
            solver_time_totals: solvers.into_iter().map(|(k, v)| (k.to_string(), v)).collect(),
            vc_kind_failure_totals: vc_failures
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect(),
            function_retry_totals: retries
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect(),
        }
    }

    fn make_history(counts: Vec<(u32, usize)>) -> Vec<FrontierSnapshot> {
        counts
            .into_iter()
            .map(|(iter, proved)| FrontierSnapshot {
                iteration: iter,
                proved_count: proved,
                failed_count: 0,
                unknown_count: 0,
                timestamp: 0,
                proved_vcs: vec![],
                failed_vcs: vec![],
            })
            .collect()
    }

    // -- Summary cards --

    #[test]
    fn test_summary_cards_basic() {
        let metrics = make_metrics(vec![3, 5, 7], vec![100, 90, 80], vec![0.2, 0.5, 0.8]);
        let cards = build_summary_cards(&metrics);

        assert_eq!(cards.len(), 5);
        assert_eq!(cards[0].title, "Total Iterations");
        assert_eq!(cards[0].value, "3");

        // VCs proven: 7 > 5 => up, green
        assert_eq!(cards[1].title, "VCs Proven (Latest)");
        assert_eq!(cards[1].value, "7");
        assert_eq!(cards[1].trend_arrow, TrendArrow::Up);
        assert_eq!(cards[1].color, CardColor::Green);

        // Time: 80 < 90 => down, green (faster is good)
        assert_eq!(cards[2].title, "Iteration Time (ms)");
        assert_eq!(cards[2].value, "80");
        assert_eq!(cards[2].trend_arrow, TrendArrow::Down);
        assert_eq!(cards[2].color, CardColor::Green);
    }

    #[test]
    fn test_summary_cards_regression() {
        let metrics = make_metrics(vec![5, 3], vec![80, 120], vec![0.1, 0.1]);
        let cards = build_summary_cards(&metrics);

        // VCs proven: 3 < 5 => down, red
        assert_eq!(cards[1].trend_arrow, TrendArrow::Down);
        assert_eq!(cards[1].color, CardColor::Red);

        // Time: 120 > 80 => up, red (slower is bad)
        assert_eq!(cards[2].trend_arrow, TrendArrow::Up);
        assert_eq!(cards[2].color, CardColor::Red);
    }

    #[test]
    fn test_summary_cards_flat() {
        let metrics = make_metrics(vec![5, 5], vec![100, 100], vec![0.5, 0.5]);
        let cards = build_summary_cards(&metrics);

        assert_eq!(cards[1].trend_arrow, TrendArrow::Flat);
        assert_eq!(cards[1].color, CardColor::Yellow);
        assert_eq!(cards[2].trend_arrow, TrendArrow::Flat);
        assert_eq!(cards[2].color, CardColor::Yellow);
    }

    #[test]
    fn test_summary_cards_single_iteration() {
        let metrics = make_metrics(vec![5], vec![100], vec![0.9]);
        let cards = build_summary_cards(&metrics);

        assert_eq!(cards[1].trend_arrow, TrendArrow::None);
        assert_eq!(cards[1].color, CardColor::Blue);
    }

    #[test]
    fn test_summary_cards_cache_color_thresholds() {
        // High cache hit rate => green
        let m1 = make_metrics(vec![5], vec![100], vec![0.8]);
        let cards1 = build_summary_cards(&m1);
        assert_eq!(cards1[3].color, CardColor::Green);

        // Medium => yellow
        let m2 = make_metrics(vec![5], vec![100], vec![0.5]);
        let cards2 = build_summary_cards(&m2);
        assert_eq!(cards2[3].color, CardColor::Yellow);

        // Low => red
        let m3 = make_metrics(vec![5], vec![100], vec![0.1]);
        let cards3 = build_summary_cards(&m3);
        assert_eq!(cards3[3].color, CardColor::Red);
    }

    // -- Convergence chart --

    #[test]
    fn test_convergence_chart_empty_history() {
        let chart = build_convergence_chart(&[]);
        assert_eq!(chart.chart_type, ChartType::Line);
        assert!(chart.data_points.is_empty());
    }

    #[test]
    fn test_convergence_chart_populated() {
        let history = make_history(vec![(0, 2), (1, 5), (2, 8)]);
        let chart = build_convergence_chart(&history);

        assert_eq!(chart.chart_type, ChartType::Line);
        assert_eq!(chart.data_points.len(), 3);
        assert!((chart.data_points[0].y - 2.0).abs() < f64::EPSILON);
        assert!((chart.data_points[2].y - 8.0).abs() < f64::EPSILON);
        assert_eq!(chart.title, "VCs Proven Over Iterations");
    }

    // -- Timing chart --

    #[test]
    fn test_timing_chart() {
        let metrics = make_metrics(vec![5, 5], vec![100, 200], vec![0.5, 0.5]);
        let chart = build_timing_chart(&metrics);

        assert_eq!(chart.chart_type, ChartType::Bar);
        assert_eq!(chart.data_points.len(), 2);
        assert!((chart.data_points[0].y - 100.0).abs() < f64::EPSILON);
        assert!((chart.data_points[1].y - 200.0).abs() < f64::EPSILON);
    }

    // -- Solver pie chart --

    #[test]
    fn test_solver_pie_chart_empty() {
        let metrics = make_metrics(vec![5], vec![100], vec![0.5]);
        let chart = build_solver_pie_chart(&metrics);

        assert_eq!(chart.chart_type, ChartType::Pie);
        assert!(chart.data_points.is_empty());
    }

    #[test]
    fn test_solver_pie_chart_populated() {
        let metrics = make_metrics_full(
            vec![5],
            vec![100],
            vec![0],
            vec![0.5],
            vec![("z4", 300), ("lean5", 100)],
            vec![],
            vec![],
        );
        let chart = build_solver_pie_chart(&metrics);

        assert_eq!(chart.chart_type, ChartType::Pie);
        assert_eq!(chart.data_points.len(), 2);
        // Sorted by time descending: z4 first
        assert_eq!(chart.data_points[0].label.as_deref(), Some("z4"));
        assert!((chart.data_points[0].y - 300.0).abs() < f64::EPSILON);
    }

    // -- Cache hit chart --

    #[test]
    fn test_cache_hit_chart() {
        let metrics = make_metrics(vec![5, 5], vec![100, 100], vec![0.3, 0.7]);
        let chart = build_cache_hit_chart(&metrics);

        assert_eq!(chart.chart_type, ChartType::Area);
        assert_eq!(chart.data_points.len(), 2);
        // Values are percentages
        assert!((chart.data_points[0].y - 30.0).abs() < f64::EPSILON);
        assert!((chart.data_points[1].y - 70.0).abs() < f64::EPSILON);
    }

    // -- Tables --

    #[test]
    fn test_tables_empty_metrics() {
        let metrics = make_metrics(vec![5], vec![100], vec![0.5]);
        let tables = build_tables(&metrics);
        assert!(tables.is_empty());
    }

    #[test]
    fn test_tables_populated() {
        let metrics = make_metrics_full(
            vec![5],
            vec![100],
            vec![0],
            vec![0.5],
            vec![("z4", 80), ("lean5", 20)],
            vec![("overflow", 5)],
            vec![("foo::bar", 3)],
        );
        let tables = build_tables(&metrics);

        assert_eq!(tables.len(), 3);

        // Solver table
        assert_eq!(tables[0].title, "Solver Performance");
        assert_eq!(tables[0].headers.len(), 3);
        assert_eq!(tables[0].rows.len(), 2);
        // z4 should be first (80 > 20)
        assert_eq!(tables[0].rows[0][0], "z4");

        // VC failures table
        assert_eq!(tables[1].title, "VC Kind Failures");
        assert_eq!(tables[1].rows.len(), 1);

        // Retries table
        assert_eq!(tables[2].title, "Function Retries");
        assert_eq!(tables[2].rows.len(), 1);
    }

    // -- Alerts --

    #[test]
    fn test_alerts_no_issues() {
        let metrics = make_metrics(vec![3, 5, 7], vec![100, 90, 80], vec![0.5, 0.5, 0.5]);
        let alerts = evaluate_alerts(&metrics);
        assert!(alerts.is_empty());
    }

    #[test]
    fn test_alerts_stagnation_detected() {
        let metrics = make_metrics(vec![5, 5, 5, 5], vec![100; 4], vec![0.5; 4]);
        let alerts = evaluate_alerts(&metrics);

        let stag = alerts.iter().find(|a| matches!(a.rule, AlertRule::StagnationDetected { .. }));
        assert!(stag.is_some(), "should detect stagnation");
        let stag = stag.unwrap();
        assert_eq!(stag.severity, AlertSeverity::Warning);
    }

    #[test]
    fn test_alerts_stagnation_critical() {
        let metrics = make_metrics(vec![5; 6], vec![100; 6], vec![0.5; 6]);
        let alerts = evaluate_alerts(&metrics);

        let stag = alerts.iter().find(|a| matches!(a.rule, AlertRule::StagnationDetected { .. }));
        assert!(stag.is_some());
        assert_eq!(stag.unwrap().severity, AlertSeverity::Critical);
    }

    #[test]
    fn test_alerts_regression_detected() {
        let metrics = make_metrics(vec![5, 7, 4], vec![100; 3], vec![0.5; 3]);
        let alerts = evaluate_alerts(&metrics);

        let reg = alerts.iter().find(|a| matches!(a.rule, AlertRule::RegressionDetected { .. }));
        assert!(reg.is_some(), "should detect regression");
    }

    #[test]
    fn test_alerts_budget_exceeded() {
        let metrics = make_metrics(vec![5, 5], vec![400_000, 300_000], vec![0.5; 2]);
        let alerts = evaluate_alerts(&metrics);

        let budget = alerts.iter().find(|a| matches!(a.rule, AlertRule::BudgetExceeded { .. }));
        assert!(budget.is_some(), "should detect budget exceeded");
        assert_eq!(budget.unwrap().severity, AlertSeverity::Critical);
    }

    #[test]
    fn test_alerts_custom_budget() {
        let metrics = make_metrics(vec![5], vec![200], vec![0.5]);
        // Budget of 100ms, total is 200ms => exceeded
        let alerts = evaluate_alerts_with_budget(&metrics, 100);
        assert!(!alerts.is_empty());
        assert!(alerts.iter().any(|a| matches!(a.rule, AlertRule::BudgetExceeded { .. })));
    }

    #[test]
    fn test_alerts_no_stagnation_when_improving() {
        let metrics = make_metrics(vec![3, 5, 7, 9], vec![100; 4], vec![0.5; 4]);
        let alerts = evaluate_alerts(&metrics);
        assert!(
            !alerts.iter().any(|a| matches!(a.rule, AlertRule::StagnationDetected { .. })),
            "should not flag stagnation when improving"
        );
    }

    // -- build_dashboard integration --

    #[test]
    fn test_build_dashboard_integration() {
        let metrics = make_metrics_full(
            vec![3, 5, 7],
            vec![100, 90, 80],
            vec![1, 2, 1],
            vec![0.2, 0.5, 0.8],
            vec![("z4", 200), ("lean5", 50)],
            vec![("overflow", 3)],
            vec![("foo::bar", 2)],
        );
        let history = make_history(vec![(0, 3), (1, 5), (2, 7)]);

        let dashboard = build_dashboard(&metrics, &history);

        assert_eq!(dashboard.summary.len(), 5);
        assert_eq!(dashboard.charts.len(), 4);
        assert_eq!(dashboard.tables.len(), 3);
        // No stagnation, no regression, no budget exceeded with default
        assert!(dashboard.alerts.is_empty());
    }

    #[test]
    fn test_build_dashboard_empty_metrics() {
        let metrics = make_metrics(vec![], vec![], vec![]);
        let history: Vec<FrontierSnapshot> = vec![];

        let dashboard = build_dashboard(&metrics, &history);

        assert_eq!(dashboard.summary.len(), 5);
        assert!(dashboard.charts[0].data_points.is_empty());
    }

    // -- Stagnation detection (delegates to stagnation::count_trailing_equal) --

    #[test]
    fn test_count_trailing_equal_none() {
        assert_eq!(count_trailing_equal(&[3, 5, 7]), 0);
    }

    #[test]
    fn test_count_trailing_equal_all_same() {
        assert_eq!(count_trailing_equal(&[5, 5, 5, 5]), 4);
    }

    #[test]
    fn test_count_trailing_equal_trailing() {
        assert_eq!(count_trailing_equal(&[3, 5, 5, 5]), 3);
    }

    #[test]
    fn test_count_trailing_equal_single() {
        assert_eq!(count_trailing_equal(&[5]), 0);
    }

    // -- Regression detection --

    #[test]
    fn test_detect_regression_none() {
        assert!(detect_regression(&[3, 5, 7]).is_none());
    }

    #[test]
    fn test_detect_regression_found() {
        let result = detect_regression(&[3, 7, 5]);
        assert_eq!(result, Some((1, 2)));
    }

    #[test]
    fn test_detect_regression_at_start() {
        let result = detect_regression(&[7, 3, 5]);
        assert_eq!(result, Some((0, 1)));
    }

    // -- Serialization --

    #[test]
    fn test_dashboard_data_serialization() {
        let metrics = make_metrics(vec![5, 7], vec![100, 90], vec![0.5, 0.7]);
        let history = make_history(vec![(0, 5), (1, 7)]);
        let dashboard = build_dashboard(&metrics, &history);

        let json = serde_json::to_string(&dashboard).expect("serialize");
        let deserialized: DashboardData = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(dashboard, deserialized);
    }
}
