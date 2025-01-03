use super::bytes::{from_bytes_wide, to_bytes};
use ff_ext::ExtensionField;
pub use transcript::BasicTranscript as Transcript;
use transcript::Transcript as IsTranscript;

/// Generate a challenge scalar
pub fn challenge_scalar<E: ExtensionField>(
  transcript: &mut Transcript<E>,
  label: &'static [u8]
) -> E {
  transcript.get_and_append_challenge(label).elements
}

/// Generate a vector of challenge scalars
pub fn challenge_vector<E: ExtensionField>(
  transcript: &mut Transcript<E>,
  label: &'static [u8],
  len: usize
) -> Vec<E> {
  (0..len)
    .map(|_i| challenge_scalar(transcript, label))
    .collect::<Vec<E>>()
}

/// Append protocol name to transcript
pub fn append_protocol_name<E: ExtensionField>(
  transcript: &mut Transcript<E>,
  protocol_name: &'static [u8]
) {
  transcript.append_message(protocol_name);
}

/// Append ExtensionField scalar to transcript
pub fn append_scalar<E: ExtensionField>(
  label: &'static [u8],
  transcript: &mut Transcript<E>,
  input: E
) {
  transcript.append_message(label);
  transcript.append_field_element_ext(&input);
}

/// Append ExtensionField scalar to transcript
pub fn append_field_to_transcript<E: ExtensionField>(
  label: &'static [u8],
  transcript: &mut Transcript<E>,
  input: E
) {
  transcript.append_message(label);
  transcript.append_field_element_ext(&input);
}

/// Append a vector ExtensionField scalars to transcript
pub fn append_field_vector_to_transcript<E: ExtensionField>(
  label: &'static [u8],
  transcript: &mut Transcript<E>,
  input: &[E],
) {
  transcript.append_message(b"begin_append_vector");
  transcript.append_field_element_exts(input);
  transcript.append_message(b"end_append_vector");
}

/// Append a message to transcript
pub fn append_message<E: ExtensionField>(
  label: &'static [u8],
  transcript: &mut Transcript<E>,
  bytes: &[u8],
) {
  transcript.append_message(label);
  transcript.append_message(bytes);
}