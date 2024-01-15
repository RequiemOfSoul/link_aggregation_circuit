use advanced_circuit_component::franklin_crypto::bellman::{Engine, PrimeField};
use advanced_circuit_component::franklin_crypto::plonk::circuit::boolean::Boolean;

fn debug_print_boolean_array_as_hex(input: &[Boolean]) {
    assert_eq!(input.len() % 8, 0);

    let mut result = vec![];

    for byte in input.chunks(8) {
        let mut byte_value = 0u8;
        for (idx, bit) in byte.iter().enumerate() {
            if let Some(value) = bit.get_value() {
                let base = if value { 1u8 } else { 0u8 };

                byte_value += base << (7 - idx);
            } else {
                return;
            }
        }

        result.push(byte_value);
    }

    println!("Value = {}", hex::encode(&result));
}

pub fn bytes_to_keep<E: Engine>() -> usize {
    (E::Fr::CAPACITY / 8) as usize
}
