use super::gfp6;

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Gfp12(pub [gfp6::Gfp6; 2]);

impl Gfp12 {
    pub fn x(&self) -> &gfp6::Gfp6 {
        &self.0[0]
    }

    pub fn y(&self) -> &gfp6::Gfp6 {
        &self.0[1]
    }
}
