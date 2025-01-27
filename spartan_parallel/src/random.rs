use ff_ext::ExtensionField;
use super::transcript::{Transcript, append_scalar, challenge_scalar, challenge_vector};
use rand::rngs::OsRng;

#[derive(Clone)]
pub struct RandomTape<E: ExtensionField> {
  tape: Transcript<E>,
  _phantom: E,
}

impl<E: ExtensionField> RandomTape<E> {
  pub fn new(name: &'static [u8]) -> Self {
    let tape = {
      let mut csprng: OsRng = OsRng;
      let mut tape = Transcript::new(name);
      append_scalar(b"init_randomness", &mut tape, E::random(&mut csprng));
      tape
    };
    Self {
      tape,
      _phantom: E::ZERO,
    }
  }

  pub fn random_scalar(&mut self, label: &'static [u8]) -> E {
    challenge_scalar(&mut self.tape, label)
  }

  pub fn random_vector(&mut self, label: &'static [u8], len: usize) -> Vec<E> {
    challenge_vector(&mut self.tape, label, len)
  }
}
