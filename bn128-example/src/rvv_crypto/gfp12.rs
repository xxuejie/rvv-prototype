use super::gfp6::Gfp6;

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Gfp12(pub [Gfp6; 2]);

impl Gfp12 {
    pub fn x(&self) -> &Gfp6 {
        &self.0[0]
    }

    pub fn y(&self) -> &Gfp6 {
        &self.0[1]
    }

    pub fn mul(&mut self, b: &Gfp12) {
        let mut tx = self.x().clone();
        tx.mul_ref(b.y());
        let mut t = b.x().clone();
        t.mul_ref(self.y());
        tx.add_ref(&t);

        let mut ty = self.y().clone();
        ty.mul_ref(b.y());
        t.set(self.x());
        t.mul_ref(b.x());
        t.mul_tau();

        self.0[0].set(&tx);
        self.0[1].set(&ty);
        self.0[1].add_ref(&t);
    }
}
