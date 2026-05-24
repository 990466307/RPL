//@compile-flags: -Z mir-opt-level=0 -Z inline-mir=false

fn main() {
    unsafe {
        let ptr = std::ptr::null::<u8>();
        let _ = core::ptr::read(ptr);
        //~^ unsafe_null_precondition

        let slice_ptr = std::ptr::null::<u8>();
        let _ = std::slice::from_raw_parts(slice_ptr, 1);
        //~^ unsafe_null_precondition

        let slice_mut_ptr = std::ptr::null_mut::<u8>();
        let _ = std::slice::from_raw_parts_mut(slice_mut_ptr, 1);
        //~^ unsafe_null_precondition

        let non_null = std::ptr::NonNull::<u8>::dangling().as_ptr();
        let _ = core::ptr::read(non_null);
    }
}
