#![no_main]
#[macro_use] extern crate libfuzzer_sys;
extern crate merge_dags;

fuzz_target!(|data: &[u8]| {
    merge_dags::run_test_stream(data, 32, 32);
});
