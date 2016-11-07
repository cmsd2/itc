
#[derive(Debug, Clone)]
pub enum IdTree {
    Leaf {
        i: bool
    },
    Node {
        left: Box<IdTree>,
        right: Box<IdTree>
    }
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
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
}

impl Stamp {
    pub fn new(i: Box<IdTree>, e: Box<EventTree>) -> Stamp {
        Stamp {
            i: i,
            e: e
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}
