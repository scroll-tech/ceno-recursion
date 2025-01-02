use ff_ext::ExtensionField;
use subtle::{Choice, CtOption};

/// Attempts to convert a little-endian byte representation of
/// a field element into an `ExtensionField`, failing if the input is not canonical.
pub fn from_bytes<E: ExtensionField>(bytes: &[u8; 32]) -> CtOption<E> {
    let mut padded = [0u8; 64];
    padded[..32].copy_from_slice(bytes);

    CtOption::new(
        E::from_uniform_bytes(&padded),
        Choice::from(1u8),
    )
}

/// Converts an element of `ExtensionField` into a byte representation in
/// little-endian byte order.
pub fn to_bytes<E: ExtensionField>(num: E) -> [u8; 32] {
    let mut res = [0; 32];
    let els = num.to_canonical_u64_vec();
    res[..8].copy_from_slice(&els[0].to_le_bytes());
    res[8..16].copy_from_slice(&els[1].to_le_bytes());
    res
}

/// Converts a 512-bit little endian integer into
/// an `ExtensionField` element by reducing by the modulus.
pub fn from_bytes_wide<E: ExtensionField>(bytes: &[u8; 64]) -> E {
    E::from_uniform_bytes(bytes).into()
}