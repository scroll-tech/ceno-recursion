use ff_ext::ExtensionField;
use goldilocks::SmallField;
use poseidon::{digest::Digest, poseidon_hash::PoseidonHash, poseidon::Poseidon, poseidon::AdaptedField};

use crate::Challenge;

// temporarily using 12-4 hashes
pub const INPUT_WIDTH: usize = 12;
pub const OUTPUT_WIDTH: usize = 4;

#[derive(Clone)]
pub struct Transcript<E: Poseidon + SmallField + AdaptedField> {
    digest: Digest<E>
}

impl<E: Poseidon + SmallField + AdaptedField> Transcript<E> {
    /// Create a new IOP transcript.
    pub fn new(label: &'static [u8]) -> Self {
        let label_f = E::bytes_to_field_elements(label);
        let digest = PoseidonHash::hash_or_noop(&label_f);
        Self {
            digest,
        }
    }
}

impl<E: Poseidon + SmallField + AdaptedField> Transcript<E> {
    /// Fork this transcript into n different threads.
    pub fn fork(self, n: usize) -> Vec<Self> {
        let mut forks = Vec::with_capacity(n);
        for i in 0..n {
            let mut fork = self.clone();
            fork.append_field_element(&(i as u64).into());
            forks.push(fork);
        }
        forks
    }

    // Append the message to the transcript.
    pub fn append_message(&mut self, msg: &[u8]) {
        let msg_f = PoseidonHash::hash_or_noop(&E::bytes_to_field_elements(msg));
        self.digest = PoseidonHash::two_to_one(&self.digest, &msg_f);
    }

    // Append the field extension element to the transcript.
    pub fn append_field_element_ext<Ext: ExtensionField::<BaseField = E>>(&mut self, element: &Ext) {
        let elem_f = PoseidonHash::hash_or_noop(element.as_bases());
        self.digest = PoseidonHash::two_to_one(&self.digest, &elem_f);
    }

    pub fn append_field_element_exts<Ext: ExtensionField::<BaseField = E>>(&mut self, element: &[Ext]) {
        for e in element {
            self.append_field_element_ext(e);
        }
    }

    // Append the field elemetn to the transcript.
    pub fn append_field_element(&mut self, element: &E) {
        let elem_f = PoseidonHash::hash_or_noop(&[element.clone()]);
        self.digest = PoseidonHash::two_to_one(&self.digest, &elem_f);
    }

    // Append the challenge to the transcript.
    pub fn append_challenge<Ext: ExtensionField::<BaseField = E>>(&mut self, challenge: Challenge<Ext>) {
        let elem_f = PoseidonHash::hash_or_noop(challenge.elements.as_bases());
        self.digest = PoseidonHash::two_to_one(&self.digest, &elem_f);
    }

    // Generate the challenge from the current transcript
    // and append it to the transcript.
    //
    // The output field element is statistical uniform as long
    // as the field has a size less than 2^384.
    pub fn get_and_append_challenge<Ext: ExtensionField::<BaseField = E>>(&mut self, label: &'static [u8]) -> Challenge<Ext> {
        self.append_message(label);

        let challenge = Challenge {
            elements: Ext::from_limbs(self.digest.elements()),
        };
        challenge
    }

    pub fn commit_rolling(&mut self) {
        // do nothing
    }

    pub fn read_field_element_ext(&self) -> E {
        unimplemented!()
    }

    pub fn read_field_element_exts<Ext: ExtensionField::<BaseField = E>>(&self) -> Vec<Ext> {
        unimplemented!()
    }

    pub fn read_field_element(&self) -> E {
        unimplemented!()
    }

    pub fn read_challenge<Ext: ExtensionField::<BaseField = E>>(&mut self) -> Challenge<Ext> {
        let r = Ext::from_bases(&self.digest.elements()[..2]);

        Challenge { elements: r }
    }

    pub fn send_challenge(&self, _challenge: E) {
        unimplemented!()
    }
}
