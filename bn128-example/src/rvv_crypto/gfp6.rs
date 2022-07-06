use super::gfp2;

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Gfp6(pub [gfp2::Gfp2; 3]);

impl Gfp6 {
    pub fn x(&self) -> &gfp2::Gfp2 {
        &self.0[0]
    }

    pub fn y(&self) -> &gfp2::Gfp2 {
        &self.0[1]
    }

    pub fn z(&self) -> &gfp2::Gfp2 {
        &self.0[2]
    }
}
