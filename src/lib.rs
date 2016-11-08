use std::cmp;

pub const N: u32 = 10000;

#[derive(Debug, Clone, PartialEq)]
pub enum IdTree {
    Leaf {
        i: bool
    },
    Node {
        left: Box<IdTree>,
        right: Box<IdTree>
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum EventTree {
    Leaf {
        n: u32
    },
    Node {
        n: u32,
        left: Box<EventTree>,
        right: Box<EventTree>
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Stamp {
    i: IdTree,
    e: EventTree
}

impl IdTree {
    pub fn zero() -> IdTree {
        IdTree::Leaf {
            i: false
        }
    }

    pub fn one() -> IdTree {
        IdTree::Leaf {
            i: true
        }
    }

    pub fn node(left: Box<IdTree>, right: Box<IdTree>) -> IdTree {
        IdTree::Node {
            left: left,
            right: right
        }
    }
}

impl EventTree {
    pub fn zero() -> EventTree {
        EventTree::leaf(0)
    }

    pub fn leaf(n: u32) -> EventTree {
        EventTree::Leaf {
            n: n
        }
    }

    pub fn node(n: u32, left: Box<EventTree>, right: Box<EventTree>) -> EventTree {
        EventTree::Node {
            n: n,
            left: left,
            right: right
        }
    }

    pub fn n(&self) -> u32 {
        match self {
            &EventTree::Leaf { n } => n,
            &EventTree::Node { n, .. } => n
        }
    }

    pub fn lift(self, m: u32) -> EventTree {
        match self {
            EventTree::Leaf { n } => EventTree::leaf(n + m),
            EventTree::Node { n, left, right } => EventTree::node(n + m, left, right)
        }
    }

    pub fn sink(self, m: u32) -> EventTree {
        match self {
            EventTree::Leaf { n } => EventTree::leaf(n - m),
            EventTree::Node { n, left, right } => EventTree::node(n - m, left, right)
        }
    }
}

impl Stamp {
    pub fn new(i: IdTree, e: EventTree) -> Stamp {
        Stamp {
            i: i,
            e: e
        }
    }

    pub fn fill(self) -> EventTree {
        if self.i == IdTree::zero() {
            self.e
        } else if self.i == IdTree::one() {
            EventTree::leaf(self.e.max())
        } else if let EventTree::Leaf {..} = self.e {
            self.e
        } else {
            if let IdTree::Node {left: ref i_left, right: ref i_right} = self.i {
                if let EventTree::Node {n, left: ref e_left, right: ref e_right} = self.e {
                    if i_left.as_ref() == &IdTree::one() {
                        let eprime_right = Stamp::new(i_right.as_ref().clone(), e_right.as_ref().clone()).fill();
                        let new_left = EventTree::leaf(cmp::max(e_left.max(), eprime_right.min()));
                        EventTree::node(n, Box::new(new_left), Box::new(eprime_right)).norm()
                    } else if i_right.as_ref() == &IdTree::one() {
                        let eprime_left = Stamp::new(i_left.as_ref().clone(), e_left.as_ref().clone()).fill();
                        let new_right = EventTree::leaf(cmp::max(e_right.max(), eprime_left.min()));
                        EventTree::node(n, Box::new(eprime_left), Box::new(new_right)).norm()
                    } else {
                        let new_left = Stamp::new(i_left.as_ref().clone(), e_left.as_ref().clone()).fill();
                        let new_right = Stamp::new(i_right.as_ref().clone(), e_right.as_ref().clone()).fill();
                        EventTree::node(n, Box::new(new_left), Box::new(new_right)).norm()
                    }
                } else {
                    unreachable!()
                }
            } else {
                unreachable!()
            }
        }
    }

    // returns event tree and cost
    pub fn grow(self) -> (EventTree, u32) {
        match self.e {
            EventTree::Leaf {n} => {
                if self.i == IdTree::one() {
                    (EventTree::leaf(n + 1), 0)
                } else {
                    let new_e = EventTree::node(n, Box::new(EventTree::zero()), Box::new(EventTree::zero()));
                    let (eprime, c) = Stamp::new(self.i.clone(), new_e).grow();
                    (eprime, c + N)
                }
            },
            EventTree::Node {n, left: e_left, right: e_right} => {
                if let IdTree::Node {left: i_left, right: i_right} = self.i {
                    if *i_left == IdTree::zero() {
                        let (eprime_right, c_right) = Stamp::new(i_right.as_ref().clone(), e_right.as_ref().clone()).grow();    
                        (EventTree::node(n, e_left, Box::new(eprime_right)), c_right + 1)
                    } else if *i_right == IdTree::zero() {
                        let (eprime_left, c_left) = Stamp::new(*i_left, *e_left).grow();
                        (EventTree::node(n, Box::new(eprime_left), e_right), c_left + 1)
                    } else {
                        let (eprime_right, c_right) = Stamp::new(*i_right, *e_right.clone()).grow();
                        let (eprime_left, c_left) = Stamp::new(*i_left, *e_left.clone()).grow();
                        if c_left < c_right {
                            (EventTree::node(n, Box::new(eprime_left), e_right), c_left + 1)
                        } else {
                            (EventTree::node(n, e_left, Box::new(eprime_right)), c_right + 1)
                        }
                    }
                } else {
                    // corrupted tree?
                    unreachable!()
                }
            }
        }
    }
}

pub trait Min<T> {
    fn min(&self) -> T; 
}

pub trait Max<T> {
    fn max(&self) -> T;
}

impl Min<u32> for EventTree {
    fn min(&self) -> u32 {
        match *self {
            EventTree::Leaf{n} => n,
            EventTree::Node{n, ref left, ref right} => n + cmp::min(left.min(), right.min())
        }
    }
}

impl Max<u32> for EventTree {
    fn max(&self) -> u32 {
        match *self {
            EventTree::Leaf{n} => n,
            EventTree::Node{n, ref left, ref right} => n + cmp::max(left.max(), right.max())
        }
    }
}

pub trait Normalisable {
    fn norm(self) -> Self;
}

impl Normalisable for IdTree {
    #[allow(non_shorthand_field_patterns)]
    fn norm(self) -> IdTree {
        match self {
            IdTree::Leaf {i: _} => {
                return self;
            }
            IdTree::Node {left, right} => {
                let norm_left = left.norm();
                let norm_right = right.norm();

                if let IdTree::Leaf{i: i1} = norm_left {
                    if let IdTree::Leaf{i: i2} = norm_right {
                        if i1 == i2 {
                            return norm_left;
                        }
                    }
                }

                return IdTree::node(Box::new(norm_left), Box::new(norm_right));
            }
        };
    }
}

impl Normalisable for EventTree {
    fn norm(self) -> EventTree {
        match self {
            EventTree::Leaf {n: _} => {
                return self;
            },
            EventTree::Node {n, left, right} => {
                let norm_left = left.norm();
                let norm_right = right.norm();

                if let EventTree::Leaf{n: m1} = norm_left {
                    if let EventTree::Leaf{n: m2} = norm_right {
                        if m1 == m2 {
                            return EventTree::leaf(n + m1);
                        }
                    }
                }

                // normalised trees have min == n
                let min_left = norm_left.n();
                let min_right = norm_right.n();

                let m = cmp::min(min_left, min_right);

                return EventTree::node(n + m, Box::new(norm_left.sink(m)), Box::new(norm_right.sink(m)));
            }
        }
    }
}

impl Normalisable for Stamp {
    fn norm(self) -> Stamp {
        Stamp::new(self.i.norm(), self.e.norm())
    }
}

pub trait LessThanOrEqual {
    fn leq(&self, other: &Self) -> bool;
}

impl LessThanOrEqual for Stamp {
    fn leq(&self, other: &Stamp) -> bool {
        self.e.leq(&other.e)
    }
}

impl LessThanOrEqual for EventTree {
    #[allow(non_shorthand_field_patterns)]
    fn leq(&self, other: &EventTree) -> bool {
        match *self {
            EventTree::Leaf {n: n1} => {
                match *other {
                    EventTree::Leaf {n: n2} => {
                        n1 <= n2
                    },
                    EventTree::Node {n: n2, ..} => {
                        n1 <= n2
                    }
                }
            },
            EventTree::Node {n: n1, left: ref left1, right: ref right1} => {
                match *other {
                    EventTree::Leaf {n: n2} => {
                        (n1 <= n2) 
                        && left1.clone().lift(n1).leq(&EventTree::leaf(n2)) 
                        && right1.clone().lift(n1).leq(&EventTree::leaf(n2))
                    },
                    EventTree::Node {n: n2, left: ref left2, right: ref right2} => {
                        (n1 <= n2)
                        && left1.clone().lift(n1).leq(&left2.clone().lift(n2))
                        && right1.clone().lift(n1).leq(&right2.clone().lift(n2))
                    }
                }
            }
        }
    }
}

pub trait Split {
    fn split(&self) -> Self;
}

impl Split for IdTree {
    fn split(&self) -> IdTree {
        match *self {
            IdTree::Leaf {i} => {
                if i {
                    IdTree::node(Box::new(IdTree::zero()), Box::new(IdTree::zero()))
                } else {
                    let new_left = Box::new(IdTree::node(Box::new(IdTree::one()), Box::new(IdTree::zero())));
                    let new_right = Box::new(IdTree::node(Box::new(IdTree::zero()), Box::new(IdTree::one())));
                    IdTree::node(new_left, new_right)
                }
            },
            IdTree::Node {ref left, ref right} => {
                if *left.as_ref() == IdTree::zero() {
                    // split always returns a Node, not a Leaf
                    if let IdTree::Node{left: i1, right: i2} = right.split() {
                        let new_left = Box::new(IdTree::node(Box::new(IdTree::zero()), i1));
                        let new_right = Box::new(IdTree::node(Box::new(IdTree::zero()), i2));
                        IdTree::node(new_left, new_right)
                    } else {
                        unreachable!()
                    }
                } else if *right.as_ref() == IdTree::zero() {
                    if let IdTree::Node{left: i1, right: i2} = left.split() {
                        let new_left = Box::new(IdTree::node(i1, Box::new(IdTree::zero())));
                        let new_right = Box::new(IdTree::node(i2, Box::new(IdTree::zero())));
                        IdTree::node(new_left, new_right)
                    } else {
                        unreachable!()
                    }
                } else {
                    let new_left = Box::new(IdTree::node(left.clone(), Box::new(IdTree::zero())));
                    let new_right = Box::new(IdTree::node(Box::new(IdTree::zero()), right.clone()));
                    IdTree::node(new_left, new_right)
                }
            }
        }
    }
}

pub trait Fork where Self: Sized {
    fn fork(&self) -> (Self, Self);
}

impl Fork for Stamp {
    fn fork(&self) -> (Stamp, Stamp) {
        match *self {
            Stamp {ref i, ref e} => {
                if let IdTree::Node {left, right} = i.split() {
                    let s1 = Stamp::new(*left, e.clone());
                    let s2 = Stamp::new(*right, e.clone());
                    (s1, s2)
                } else {
                    unreachable!()
                }
            }
        }
    }
}

pub trait Sum {
    fn sum(&self, other: &Self) -> Self;
}

impl Sum for IdTree {
    #[allow(non_shorthand_field_patterns)]
    fn sum(&self, other: &IdTree) -> IdTree {
        if *self == IdTree::zero() {
            return other.clone();
        } else if *other == IdTree::zero() {
            return self.clone();
        }

        if let IdTree::Node {left: ref left1, right: ref right1} = *self {
            if let IdTree::Node {left: ref left2, right: ref right2} = *other {
                let new_left = Box::new(left1.sum(left2));
                let new_right = Box::new(right1.sum(right2));
                return IdTree::node(new_left, new_right).norm();
            } else {
                // corrupted tree?
                unreachable!();
            }
        } else {
            // corrupted tree?
            unreachable!();
        }
    }
}

pub trait Join where Self: Sized {
    fn join(&self, other: &Self) -> Self;
}

impl Join for Stamp {
    fn join(&self, other: &Stamp) -> Stamp {
        let sum_i = self.i.sum(&other.i);
        let join_e = self.e.join(&other.e);
        Stamp::new(sum_i, join_e)
    }
}

impl Join for EventTree {
    fn join(&self, other: &EventTree) -> EventTree {
        match *self {
            EventTree::Leaf {n: n1} => {
                match *other {
                    EventTree::Leaf {n: n2} => {
                        EventTree::leaf(cmp::max(n1, n2))
                    },
                    EventTree::Node {..} => {
                        let new_left = EventTree::node(n1, Box::new(EventTree::zero()), Box::new(EventTree::zero()));
                        new_left.join(other)
                    }
                }
            },
            EventTree::Node {n: n1, left: ref left1, right: ref right1} => {
                match *other {
                    EventTree::Leaf {n: n2} => {
                        let new_right = EventTree::node(n2, Box::new(EventTree::zero()), Box::new(EventTree::zero()));
                        self.join(&new_right)
                    },
                    EventTree::Node {n: n2, left: ref left2, right: ref right2} => {
                        if n1 > n2 {
                            other.join(self)
                        } else {
                            let new_left = left1.join(&left2.clone().lift(n2 - n1));
                            let new_right = right1.join(&right2.clone().lift(n2 - n1));
                            EventTree::node(n1, Box::new(new_left), Box::new(new_right)).norm()
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn norm_id_one_is_one() {
        let idt = IdTree::one();
        let nidt = idt.norm();
        assert_eq!(nidt, IdTree::one());
    }

    #[test]
    fn norm_id_zero_is_zero() {
        let idt = IdTree::zero();
        let nidt = idt.norm();
        assert_eq!(nidt, IdTree::zero());
    }

    #[test]
    fn norm_id_0_0_is_0() {
        let idt = IdTree::node(Box::new(IdTree::zero()), Box::new(IdTree::zero()));
        let nidt = idt.norm();
        assert_eq!(nidt, IdTree::zero());
    }

    #[test]
    fn norm_id_1_1_is_1() {
        let idt = IdTree::node(Box::new(IdTree::one()), Box::new(IdTree::one()));
        let nidt = idt.norm();
        assert_eq!(nidt, IdTree::one());
    }

    #[test]
    fn norm_id_0_1_is_0_1() {
        let idt = IdTree::node(Box::new(IdTree::one()), Box::new(IdTree::zero()));
        let nidt = idt.clone().norm();
        assert_eq!(nidt, idt);
    }

    #[test]
    fn norm_id_1_1_1_is_1() {
        let idt = IdTree::node(Box::new(IdTree::one()), Box::new(IdTree::node(Box::new(IdTree::one()), Box::new(IdTree::one()))));
        let nidt = idt.clone().norm();
        assert_eq!(nidt, IdTree::one());
    }

    // (2, 1, 1) ~=~ 3
    #[test]
    fn norm_e_one() {
        let et = EventTree::node(2, Box::new(EventTree::leaf(1)), Box::new(EventTree::leaf(1)));
        let net = et.clone().norm();
        assert_eq!(net, EventTree::leaf(3));
    }

    // (2, (2, 1, 0), 3) ~=~ (4, (0, 1, 0), 1)
    #[test]
    fn norm_e_two() {
        let a = Box::new(EventTree::node(2, Box::new(EventTree::leaf(1)), Box::new(EventTree::leaf(0))));
        let b = Box::new(EventTree::leaf(3));
        let et = EventTree::node(2, a, b);

        let expected_a = Box::new(EventTree::node(0, Box::new(EventTree::leaf(1)), Box::new(EventTree::leaf(0))));
        let expected_b = Box::new(EventTree::leaf(1));
        let expected = EventTree::node(4, expected_a, expected_b);

        let net = et.norm();

        assert_eq!(net, expected);
    }
}
