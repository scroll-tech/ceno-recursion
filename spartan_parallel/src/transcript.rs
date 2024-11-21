use super::scalar::SpartanExtensionField;
use merlin::Transcript;

pub trait ProofTranscript<S: SpartanExtensionField> {
  fn append_protocol_name(&mut self, protocol_name: &'static [u8]);
  fn append_scalar(&mut self, label: &'static [u8], scalar: &S);
  fn challenge_scalar(&mut self, label: &'static [u8]) -> S;
  fn challenge_vector(&mut self, label: &'static [u8], len: usize) -> Vec<S>;
}

impl<S: SpartanExtensionField> ProofTranscript<S> for Transcript {
  fn append_protocol_name(&mut self, protocol_name: &'static [u8]) {
    self.append_message(b"protocol-name", protocol_name);
  }

  fn append_scalar(&mut self, label: &'static [u8], scalar: &S) {
    self.append_message(label, &scalar.to_bytes());
  }

  fn challenge_scalar(&mut self, label: &'static [u8]) -> S {
    let mut buf = [0u8; 64];
    self.challenge_bytes(label, &mut buf);
    S::from_bytes_wide(&buf)
  }

  fn challenge_vector(&mut self, label: &'static [u8], len: usize) -> Vec<S> {
    (0..len)
      .map(|_i| self.challenge_scalar(label))
      .collect::<Vec<S>>()
  }
}

pub trait AppendToTranscript {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript);
}
