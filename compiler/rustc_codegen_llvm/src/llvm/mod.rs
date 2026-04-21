#![allow(non_snake_case)]

use std::ffi::{CStr, CString};
use std::num::NonZero;
use std::ptr;
use std::string::FromUtf8Error;

use libc::c_uint;
use rustc_abi::{AddressSpace, Align, Size, WrappingRange};
use rustc_llvm::RustString;

pub(crate) use self::CallConv::*;
pub(crate) use self::CodeGenOptSize::*;
pub(crate) use self::conversions::*;
pub(crate) use self::ffi::*;
pub(crate) use self::metadata_kind::*;
use crate::common::AsCCharPtr;

mod conversions;
pub(crate) mod diagnostic;
pub(crate) mod enzyme_ffi;
mod ffi;
mod metadata_kind;

pub(crate) use self::enzyme_ffi::*;

impl LLVMRustResult {
    pub(crate) fn into_result(self) -> Result<(), ()> {
        match self {
            LLVMRustResult::Success => Ok(()),
            LLVMRustResult::Failure => Err(()),
        }
    }
}

pub(crate) fn AddFunctionAttributes<'ll>(
    llfn: &'ll Value,
    idx: AttributePlace,
    attrs: &[&'ll Attribute],
) {
    // SAFETY: `llfn` is a valid LLVM function value, all attributes in the slice are valid, and the index specifies a valid attribute location (function, return, or parameter).
    unsafe {
        LLVMRustAddFunctionAttributes(llfn, idx.as_uint(), attrs.as_ptr(), attrs.len());
    }
}

pub(crate) fn HasStringAttribute<'ll>(llfn: &'ll Value, name: &str) -> bool {
    // SAFETY: `llfn` is a valid LLVM function value, and the name buffer and length specify a valid attribute string.
    unsafe { LLVMRustHasFnAttribute(llfn, name.as_c_char_ptr(), name.len()) }
}

pub(crate) fn RemoveStringAttrFromFn<'ll>(llfn: &'ll Value, name: &str) {
    // SAFETY: `llfn` is a valid LLVM function value, and the name buffer and length specify a valid attribute string.
    unsafe { LLVMRustRemoveFnAttribute(llfn, name.as_c_char_ptr(), name.len()) }
}

pub(crate) fn AddCallSiteAttributes<'ll>(
    callsite: &'ll Value,
    idx: AttributePlace,
    attrs: &[&'ll Attribute],
) {
    // SAFETY: The call-site instruction is a valid LLVM call or invoke, all attributes are valid, and the index specifies a valid attribute location.
    unsafe {
        LLVMRustAddCallSiteAttributes(callsite, idx.as_uint(), attrs.as_ptr(), attrs.len());
    }
}

pub(crate) fn CreateAttrStringValue<'ll>(
    llcx: &'ll Context,
    attr: &str,
    value: &str,
) -> &'ll Attribute {
    // SAFETY: The LLVM context is valid, and the attribute name/value string buffers and lengths are valid.
    unsafe {
        LLVMCreateStringAttribute(
            llcx,
            attr.as_c_char_ptr(),
            attr.len().try_into().expect("invariant: value fits in target type"),
            value.as_c_char_ptr(),
            value.len().try_into().expect("invariant: value fits in target type"),
        )
    }
}

pub(crate) fn CreateAttrString<'ll>(llcx: &'ll Context, attr: &str) -> &'ll Attribute {
    // SAFETY: The LLVM context is valid, and the attribute name/value string buffers and lengths are valid.
    unsafe {
        LLVMCreateStringAttribute(
            llcx,
            attr.as_c_char_ptr(),
            attr.len().try_into().expect("invariant: value fits in target type"),
            std::ptr::null(),
            0,
        )
    }
}

pub(crate) fn CreateAlignmentAttr(llcx: &Context, bytes: u64) -> &Attribute {
    // SAFETY: `llcx` is a valid LLVM context, and `bytes` is a valid alignment value (power of two).
    unsafe { LLVMRustCreateAlignmentAttr(llcx, bytes) }
}

pub(crate) fn CreateDereferenceableAttr(llcx: &Context, bytes: u64) -> &Attribute {
    // SAFETY: `llcx` is a valid LLVM context, and `bytes` specifies the dereferenceable byte count.
    unsafe { LLVMRustCreateDereferenceableAttr(llcx, bytes) }
}

pub(crate) fn CreateDereferenceableOrNullAttr(llcx: &Context, bytes: u64) -> &Attribute {
    // SAFETY: `llcx` is a valid LLVM context, and `bytes` specifies the dereferenceable byte count.
    unsafe { LLVMRustCreateDereferenceableOrNullAttr(llcx, bytes) }
}

pub(crate) fn CreateByValAttr<'ll>(llcx: &'ll Context, ty: &'ll Type) -> &'ll Attribute {
    // SAFETY: `llcx` is a valid LLVM context, and `ty` is a valid LLVM type.
    unsafe { LLVMRustCreateByValAttr(llcx, ty) }
}

pub(crate) fn CreateStructRetAttr<'ll>(llcx: &'ll Context, ty: &'ll Type) -> &'ll Attribute {
    // SAFETY: `llcx` is a valid LLVM context, and `ty` is a valid LLVM type.
    unsafe { LLVMRustCreateStructRetAttr(llcx, ty) }
}

pub(crate) fn CreateUWTableAttr(llcx: &Context, async_: bool) -> &Attribute {
    // SAFETY: `llcx` is a valid LLVM context.
    unsafe { LLVMRustCreateUWTableAttr(llcx, async_) }
}

pub(crate) fn CreateAllocSizeAttr(llcx: &Context, size_arg: u32) -> &Attribute {
    // SAFETY: `llcx` is a valid LLVM context, and `size_arg` is a valid parameter index.
    unsafe { LLVMRustCreateAllocSizeAttr(llcx, size_arg) }
}

pub(crate) fn CreateAllocKindAttr(llcx: &Context, kind_arg: AllocKindFlags) -> &Attribute {
    // SAFETY: `llcx` is a valid LLVM context, and the kind flags are valid alloc-kind bits.
    unsafe { LLVMRustCreateAllocKindAttr(llcx, kind_arg.bits()) }
}

pub(crate) fn CreateRangeAttr(llcx: &Context, size: Size, range: WrappingRange) -> &Attribute {
    let lower = range.start;
    // LLVM treats the upper bound as exclusive, but allows wrapping.
    let upper = range.end.wrapping_add(1);

    // Pass each `u128` endpoint value as a `[u64; 2]` array, least-significant part first.
    let as_u64_array = |x: u128| [x as u64, (x >> 64) as u64];
    let lower_words: [u64; 2] = as_u64_array(lower);
    let upper_words: [u64; 2] = as_u64_array(upper);

    // To ensure that LLVM doesn't try to read beyond the `[u64; 2]` arrays,
    // we must explicitly check that `size_bits` does not exceed 128.
    let size_bits = size.bits();
    assert!(size_bits <= 128);
    // More robust assertions that are redundant with `size_bits <= 128` and
    // should be optimized away.
    assert!(size_bits.div_ceil(64) <= u64::try_from(lower_words.len()).expect("invariant: value fits in target type"));
    assert!(size_bits.div_ceil(64) <= u64::try_from(upper_words.len()).expect("invariant: value fits in target type"));
    let size_bits = c_uint::try_from(size_bits).expect("invariant: value fits in target type");

    // SAFETY: The LLVM context is valid, the bit width is valid, and the lower/upper bound word arrays are valid.
    unsafe {
        LLVMRustCreateRangeAttribute(llcx, size_bits, lower_words.as_ptr(), upper_words.as_ptr())
    }
}

#[derive(Copy, Clone)]
pub(crate) enum AttributePlace {
    ReturnValue,
    Argument(u32),
    Function,
}

impl AttributePlace {
    pub(crate) fn as_uint(self) -> c_uint {
        match self {
            AttributePlace::ReturnValue => 0,
            AttributePlace::Argument(i) => 1 + i,
            AttributePlace::Function => !0,
        }
    }
}

#[derive(Copy, Clone, PartialEq)]
#[repr(C)]
pub(crate) enum CodeGenOptSize {
    CodeGenOptSizeNone = 0,
    CodeGenOptSizeDefault = 1,
    CodeGenOptSizeAggressive = 2,
}

pub(crate) fn SetInstructionCallConv(instr: &Value, cc: CallConv) {
    // SAFETY: The instruction is a valid LLVM call or invoke instruction, and the calling convention value is valid.
    unsafe {
        LLVMSetInstructionCallConv(instr, cc as c_uint);
    }
}
pub(crate) fn SetFunctionCallConv(fn_: &Value, cc: CallConv) {
    // SAFETY: The function is a valid LLVM function value, and the calling convention value is valid.
    unsafe {
        LLVMSetFunctionCallConv(fn_, cc as c_uint);
    }
}

// Externally visible symbols that might appear in multiple codegen units need to appear in
// their own comdat section so that the duplicates can be discarded at link time. This can for
// example happen for generics when using multiple codegen units. This function simply uses the
// value's name as the comdat value to make sure that it is in a 1-to-1 relationship to the
// function.
// For more details on COMDAT sections see e.g., https://www.airs.com/blog/archives/52
pub(crate) fn SetUniqueComdat(llmod: &Module, val: &Value) {
    let name_buf = get_value_name(val);
    let name =
        CString::from_vec_with_nul(name_buf).or_else(|buf| CString::new(buf.into_bytes())).expect("invariant: CString::new failed - input contains null byte");
    set_comdat(llmod, val, &name);
}

pub(crate) fn set_unnamed_address(global: &Value, unnamed: UnnamedAddr) {
    LLVMSetUnnamedAddress(global, unnamed);
}

pub(crate) fn set_thread_local_mode(global: &Value, mode: ThreadLocalMode) {
    // SAFETY: The global variable is a valid LLVM reference, and the mode is a valid thread-local mode.
    unsafe {
        LLVMSetThreadLocalMode(global, mode);
    }
}

impl AttributeKind {
    /// Create an LLVM Attribute with no associated value.
    pub(crate) fn create_attr(self, llcx: &Context) -> &Attribute {
        // SAFETY: `llcx` is a valid LLVM context, and the attribute kind is a valid LLVM attribute enum value.
        unsafe { LLVMRustCreateAttrNoValue(llcx, self) }
    }
}

impl MemoryEffects {
    /// Create an LLVM Attribute with these memory effects.
    pub(crate) fn create_attr(self, llcx: &Context) -> &Attribute {
        // SAFETY: `llcx` is a valid LLVM context, and the memory effects value is a valid bitmask.
        unsafe { LLVMRustCreateMemoryEffectsAttr(llcx, self) }
    }
}

pub(crate) fn set_section(llglobal: &Value, section_name: &CStr) {
    // SAFETY: The global value is a valid LLVM reference, and the section name is a valid C string.
    unsafe {
        LLVMSetSection(llglobal, section_name.as_ptr());
    }
}

pub(crate) fn add_global<'a>(llmod: &'a Module, ty: &'a Type, name_cstr: &CStr) -> &'a Value {
    // SAFETY: `self.llmod` is a valid LLVM module, `ty` is a valid LLVM type, and the name is a valid C string.
    unsafe { LLVMAddGlobal(llmod, ty, name_cstr.as_ptr()) }
}

pub(crate) fn set_initializer(llglobal: &Value, constant_val: &Value) {
    // SAFETY: The global variable and initializer are valid LLVM references, and the initializer's type matches the global's value type.
    unsafe {
        LLVMSetInitializer(llglobal, constant_val);
    }
}

pub(crate) fn set_global_constant(llglobal: &Value, is_constant: bool) {
    LLVMSetGlobalConstant(llglobal, is_constant.to_llvm_bool());
}

pub(crate) fn get_linkage(llglobal: &Value) -> Linkage {
    // SAFETY: The global value is a valid LLVM reference.
    unsafe { LLVMGetLinkage(llglobal) }.to_rust()
}

pub(crate) fn set_linkage(llglobal: &Value, linkage: Linkage) {
    // SAFETY: The global value is a valid LLVM reference.
    unsafe {
        LLVMSetLinkage(llglobal, linkage);
    }
}

pub(crate) fn is_declaration(llglobal: &Value) -> bool {
    // SAFETY: The global value is a valid LLVM reference.
    unsafe { LLVMIsDeclaration(llglobal) }.is_true()
}

pub(crate) fn get_visibility(llglobal: &Value) -> Visibility {
    // SAFETY: The global value is a valid LLVM reference.
    unsafe { LLVMGetVisibility(llglobal) }.to_rust()
}

pub(crate) fn set_visibility(llglobal: &Value, visibility: Visibility) {
    // SAFETY: The global value is a valid LLVM reference.
    unsafe {
        LLVMSetVisibility(llglobal, visibility);
    }
}

pub(crate) fn set_alignment(llglobal: &Value, align: Align) {
    // SAFETY: The value is a valid LLVM global, alloca, load, or store instruction, and the alignment is a valid power of two.
    unsafe {
        ffi::LLVMSetAlignment(llglobal, align.bytes() as c_uint);
    }
}

pub(crate) fn set_externally_initialized(llglobal: &Value, is_ext_init: bool) {
    LLVMSetExternallyInitialized(llglobal, is_ext_init.to_llvm_bool());
}

/// Get the `name`d comdat from `llmod` and assign it to `llglobal`.
///
/// Inserts the comdat into `llmod` if it does not exist.
/// It is an error to call this if the target does not support comdat.
pub(crate) fn set_comdat(llmod: &Module, llglobal: &Value, name: &CStr) {
    // SAFETY: `llfn` is a valid LLVM function value, and the index is within the function's parameter count.
    unsafe {
        let comdat = LLVMGetOrInsertComdat(llmod, name.as_ptr());
        LLVMSetComdat(llglobal, comdat);
    }
}

pub(crate) fn count_params(llfn: &Value) -> c_uint {
    LLVMCountParams(llfn)
}

/// Safe wrapper around `LLVMGetParam`, because segfaults are no fun.
pub(crate) fn get_param(llfn: &Value, index: c_uint) -> &Value {
    // SAFETY: `llfn` is a valid LLVM function value, and the index is within the function's parameter count.
    unsafe {
        assert!(
            index < LLVMCountParams(llfn),
            "out of bounds argument access: {} out of {} arguments",
            index,
            LLVMCountParams(llfn)
        );
        LLVMGetParam(llfn, index)
    }
}

/// Safe wrapper for `LLVMGetValueName2`
/// Needs to allocate the value, because `set_value_name` will invalidate
/// the pointer.
pub(crate) fn get_value_name(value: &Value) -> Vec<u8> {
    // SAFETY: The pointer is valid for `len` elements, the data is properly aligned, and the lifetime of the resulting slice does not exceed the source's.
    unsafe {
        let mut len = 0;
        let data = LLVMGetValueName2(value, &mut len);
        std::slice::from_raw_parts(data.cast(), len).to_vec()
    }
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct Intrinsic {
    id: NonZero<c_uint>,
}

impl Intrinsic {
    pub(crate) fn lookup(name: &[u8]) -> Option<Self> {
        // SAFETY: The name buffer and length are valid.
        let id = unsafe { LLVMLookupIntrinsicID(name.as_c_char_ptr(), name.len()) };
        NonZero::new(id).map(|id| Self { id })
    }

    pub(crate) fn get_declaration<'ll>(
        self,
        llmod: &'ll Module,
        type_params: &[&'ll Type],
    ) -> &'ll Value {
        // SAFETY: The module is valid, the intrinsic ID is valid, and the parameter types slice contains valid LLVM types.
        unsafe {
            LLVMGetIntrinsicDeclaration(llmod, self.id, type_params.as_ptr(), type_params.len())
        }
    }
}

/// Safe wrapper for `LLVMSetValueName2` from a byte slice
pub(crate) fn set_value_name(value: &Value, name: &[u8]) {
    // SAFETY: The value is a valid LLVM reference, and the name buffer and length are valid.
    unsafe {
        let data = name.as_c_char_ptr();
        LLVMSetValueName2(value, data, name.len());
    }
}

pub(crate) fn build_string(f: impl FnOnce(&RustString)) -> Result<String, FromUtf8Error> {
    String::from_utf8(RustString::build_byte_buffer(f))
}

pub(crate) fn build_byte_buffer(f: impl FnOnce(&RustString)) -> Vec<u8> {
    RustString::build_byte_buffer(f)
}

pub(crate) fn twine_to_string(tr: &Twine) -> String {
    // SAFETY: The output function pointer is valid, and the LLVM value/type being printed is a valid reference.
    unsafe {
        build_string(|s| LLVMRustWriteTwineToString(tr, s)).expect("got a non-UTF8 Twine from LLVM")
    }
}

pub(crate) fn last_error() -> Option<String> {
    // SAFETY: Reads the thread-local LLVM error string. The returned pointer is valid until the next LLVM call on this thread.
    unsafe {
        let cstr = LLVMRustGetLastError();
        if cstr.is_null() {
            None
        } else {
            let err = CStr::from_ptr(cstr).to_bytes();
            let err = String::from_utf8_lossy(err).to_string();
            libc::free(cstr as *mut _);
            Some(err)
        }
    }
}

/// Owning pointer to an [`OperandBundle`] that will dispose of the bundle
/// when dropped.
pub(crate) struct OperandBundleBox<'a> {
    raw: ptr::NonNull<OperandBundle<'a>>,
}

impl<'a> OperandBundleBox<'a> {
    pub(crate) fn new(name: &str, vals: &[&'a Value]) -> Self {
        // SAFETY: The tag string and LLVM value operands are valid references.
        let raw = unsafe {
            LLVMCreateOperandBundle(
                name.as_c_char_ptr(),
                name.len(),
                vals.as_ptr(),
                vals.len() as c_uint,
            )
        };
        Self { raw: ptr::NonNull::new(raw).expect("invariant: pointer is non-null") }
    }

    /// Dereferences to the underlying `&OperandBundle`.
    ///
    /// This can't be a `Deref` implementation because `OperandBundle` transitively
    /// contains an extern type, which is incompatible with `Deref::Target: ?Sized`.
    pub(crate) fn as_ref(&self) -> &OperandBundle<'a> {
        // SAFETY: The returned reference is opaque and can only used for FFI.
        // It is valid for as long as `&self` is.
        unsafe { self.raw.as_ref() }
    }
}

impl Drop for OperandBundleBox<'_> {
    fn drop(&mut self) {
        // SAFETY: The module is valid, and the key buffer, length, and flag value are valid.
        unsafe {
            LLVMDisposeOperandBundle(self.raw);
        }
    }
}

pub(crate) fn add_module_flag_u32(
    module: &Module,
    merge_behavior: ModuleFlagMergeBehavior,
    key: &str,
    value: u32,
) {
    // SAFETY: The module is valid, and the key buffer, length, and flag value are valid.
    unsafe {
        LLVMRustAddModuleFlagU32(module, merge_behavior, key.as_c_char_ptr(), key.len(), value);
    }
}

pub(crate) fn add_module_flag_str(
    module: &Module,
    merge_behavior: ModuleFlagMergeBehavior,
    key: &str,
    value: &str,
) {
    // SAFETY: The module is valid, and the key/value buffers and their lengths are valid.
    unsafe {
        LLVMRustAddModuleFlagString(
            module,
            merge_behavior,
            key.as_c_char_ptr(),
            key.len(),
            value.as_c_char_ptr(),
            value.len(),
        );
    }
}

pub(crate) fn set_dllimport_storage_class<'ll>(v: &'ll Value) {
    // SAFETY: The global value is a valid LLVM reference, and the storage class is a valid DLL storage class value.
    unsafe {
        LLVMSetDLLStorageClass(v, DLLStorageClass::DllImport);
    }
}

pub(crate) fn set_dso_local<'ll>(v: &'ll Value) {
    // SAFETY: The global value is a valid LLVM reference.
    unsafe {
        LLVMRustSetDSOLocal(v, true);
    }
}

/// Safe wrapper for `LLVMAppendModuleInlineAsm`, which delegates to
/// `Module::appendModuleInlineAsm`.
pub(crate) fn append_module_inline_asm<'ll>(llmod: &'ll Module, asm: &[u8]) {
    // SAFETY: The module is valid, and the assembly string buffer and length are valid.
    unsafe {
        LLVMAppendModuleInlineAsm(llmod, asm.as_ptr(), asm.len());
    }
}

/// Safe wrapper for `LLVMAddAlias2`
pub(crate) fn add_alias<'ll>(
    module: &'ll Module,
    ty: &Type,
    address_space: AddressSpace,
    aliasee: &Value,
    name: &CStr,
) -> &'ll Value {
    // SAFETY: The module, value type, address space, aliasee, and name are all valid.
    unsafe { LLVMAddAlias2(module, ty, address_space.0, aliasee, name.as_ptr()) }
}
