pub struct List {
    head: Link,
}

enum Link {
    Empty,
    More(Box<Node>)
}

struct Node {
    elem: i32,
    next: Link,
}

impl List {
    // Self is an alias for the type that we currently implement
    pub fn new() -> Self {
        List {
            head: Link::Empty
        }
    }
}