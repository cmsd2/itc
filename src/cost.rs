
use std::cmp;
use std::ops::Add;

#[derive(Debug, Clone, PartialEq)]
pub enum Cost {
    Small(u32),
    Big(u32, Box<Cost>)
}

impl PartialOrd for Cost {
    fn partial_cmp(&self, rhs: &Cost) -> Option<cmp::Ordering> {
        match *self {
            Cost::Small(l) => {
                if let Cost::Small(r) = *rhs {
                    PartialOrd::partial_cmp(&l, &r)
                } else {
                    Some(cmp::Ordering::Less)
                }
            },
            Cost::Big(l, ref cl) => {
                if let Cost::Big(r, ref cr) = *rhs {
                    if let Some(eq) = PartialOrd::partial_cmp(cl.as_ref(), cr.as_ref()) {
                        if eq == cmp::Ordering::Equal {
                            PartialOrd::partial_cmp(&l, &r)
                        } else {
                            Some(eq)
                        }
                    } else {
                        None
                    }
                } else {
                    Some(cmp::Ordering::Greater)
                }
            }
        }
    }
}

impl Add<u32> for Cost {
    type Output = Self;

    fn add(self, n: u32) -> Cost {
        match self {
            Cost::Small(m) => {
                Cost::Small(m + n)
            },
            Cost::Big(m, c) => {
                Cost::Big(m + n, c)
            }
        }
    }
}

impl Cost {
    pub fn zero() -> Cost {
        Cost::Small(0)
    }

    pub fn shift(self) -> Cost {
        match self {
            Cost::Small(_n) => Cost::Big(0, Box::new(self)),
            Cost::Big(n, c) => Cost::Big(0, Box::new(c.shift() + n))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Cost;

    #[test]
    fn test_cmp_small() {
        let a = Cost::zero();
        let b = a.clone() + 1;

        assert!(a < b);
        assert!(b > a);
    }

    #[test]
    fn test_cmp_big() {
        let a = Cost::zero().shift() + 1;
        let b = (Cost::zero() + 1).shift();

        assert!(a < b);
        assert!(b > a);
    }

    #[test]
    fn test_cmp_mixed() {
        let a = Cost::zero() + 1;
        let b = (Cost::zero() + 1).shift();

        assert!(a < b);
        assert!(b > a);
    }
}