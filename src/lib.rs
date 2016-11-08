use std::cmp;

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
    i: Box<IdTree>,
    e: Box<EventTree>
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

    pub fn lift(self, m: u32) -> Box<EventTree> {
        match self {
            EventTree::Leaf { n } => Box::new(EventTree::leaf(n + m)),
            EventTree::Node { n, left, right } => Box::new(EventTree::node(n + m, left, right))
        }
    }

    pub fn sink(self, m: u32) -> Box<EventTree> {
        match self {
            EventTree::Leaf { n } => Box::new(EventTree::leaf(n - m)),
            EventTree::Node { n, left, right } => Box::new(EventTree::node(n - m, left, right))
        }
    }
}

impl Stamp {
    pub fn new(i: Box<IdTree>, e: Box<EventTree>) -> Stamp {
        Stamp {
            i: i,
            e: e
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
    fn norm(self) -> Box<Self>;
}

impl Normalisable for IdTree {
    #[allow(non_shorthand_field_patterns)]
    fn norm(self) -> Box<IdTree> {
        match self {
            IdTree::Leaf {i: _} => {
                return Box::new(self);
            }
            IdTree::Node {left, right} => {
                let norm_left = left.norm();
                let norm_right = right.norm();

                if let &IdTree::Leaf{i: i1} = norm_left.as_ref() {
                    if let &IdTree::Leaf{i: i2} = norm_right.as_ref() {
                        if i1 == i2 {
                            return norm_left;
                        }
                    }
                }

                return Box::new(IdTree::Node{left: norm_left, right: norm_right})
            }
        };
    }
}

impl Normalisable for EventTree {
    fn norm(self) -> Box<EventTree> {
        match self {
            EventTree::Leaf {n: _} => {
                return Box::new(self);
            },
            EventTree::Node {n, left, right} => {
                let norm_left = left.norm();
                let norm_right = right.norm();

                if let &EventTree::Leaf{n: m1} = norm_left.as_ref() {
                    if let &EventTree::Leaf{n: m2} = norm_right.as_ref() {
                        if m1 == m2 {
                            return Box::new(EventTree::leaf(n + m1));
                        }
                    }
                }

                // normalised trees have min == n
                let min_left = norm_left.n();
                let min_right = norm_right.n();

                let m = cmp::min(min_left, min_right);

                return Box::new(EventTree::node(n + m, norm_left.sink(m), norm_right.sink(m)));
            }
        }
    }
}

impl Normalisable for Stamp {
    fn norm(self) -> Box<Stamp> {
        Box::new(Stamp::new(self.i.norm(), self.e.norm()))
    }
}

pub trait LessThanOrEqual {
    fn leq(&self, other: &Self) -> bool;
}

impl LessThanOrEqual for Stamp {
    fn leq(&self, other: &Stamp) -> bool {
        self.e.leq(other.e.as_ref())
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn norm_id_one_is_one() {
        let idt = IdTree::one();
        let nidt = idt.norm();
        assert_eq!(*nidt, IdTree::one());
    }

    #[test]
    fn norm_id_zero_is_zero() {
        let idt = IdTree::zero();
        let nidt = idt.norm();
        assert_eq!(*nidt, IdTree::zero());
    }

    #[test]
    fn norm_id_0_0_is_0() {
        let idt = IdTree::node(Box::new(IdTree::zero()), Box::new(IdTree::zero()));
        let nidt = idt.norm();
        assert_eq!(*nidt, IdTree::zero());
    }

    #[test]
    fn norm_id_1_1_is_1() {
        let idt = IdTree::node(Box::new(IdTree::one()), Box::new(IdTree::one()));
        let nidt = idt.norm();
        assert_eq!(*nidt, IdTree::one());
    }

    #[test]
    fn norm_id_0_1_is_0_1() {
        let idt = IdTree::node(Box::new(IdTree::one()), Box::new(IdTree::zero()));
        let nidt = idt.clone().norm();
        assert_eq!(*nidt, idt);
    }

    #[test]
    fn norm_id_1_1_1_is_1() {
        let idt = IdTree::node(Box::new(IdTree::one()), Box::new(IdTree::node(Box::new(IdTree::one()), Box::new(IdTree::one()))));
        let nidt = idt.clone().norm();
        assert_eq!(*nidt, IdTree::one());
    }

    // (2, 1, 1) ~=~ 3
    #[test]
    fn norm_e_one() {
        let et = EventTree::node(2, Box::new(EventTree::leaf(1)), Box::new(EventTree::leaf(1)));
        let net = et.clone().norm();
        assert_eq!(*net, EventTree::leaf(3));
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

        assert_eq!(*net, expected);
    }
}
