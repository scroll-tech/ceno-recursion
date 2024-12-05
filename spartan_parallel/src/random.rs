use super::scalar::SpartanExtensionField;
use super::transcript::ProofTranscript;
use merlin::Transcript;
use rand::rngs::OsRng;

#[derive(Clone)]
pub struct RandomTape<S: SpartanExtensionField> {
  tape: Transcript,
  _phantom: S,
}

impl<S: SpartanExtensionField> RandomTape<S> {
  pub fn new(name: &'static [u8]) -> Self {
    let tape = {
      let mut csprng: OsRng = OsRng;
      let mut tape = Transcript::new(name);
      tape.append_scalar(b"init_randomness", &S::random(&mut csprng));
      tape
    };
    Self {
      tape,
      _phantom: S::field_zero(),
    }
  }

  pub fn random_scalar(&mut self, label: &'static [u8]) -> S {
    self.tape.challenge_scalar(label)
  }

  pub fn random_vector(&mut self, label: &'static [u8], len: usize) -> Vec<S> {
    self.tape.challenge_vector(label, len)
  }
}
