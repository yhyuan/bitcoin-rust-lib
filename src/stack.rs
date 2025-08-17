// Custom double-linked list node
struct Node<T> {
    value: T,
    next: Option<*mut Node<T>>,
    prev: Option<*mut Node<T>>,
}

struct LinkedList<T> {
    head: Option<*mut Node<T>>,
    tail: Option<*mut Node<T>>,
}

impl<T> LinkedList<T> {
    fn new() -> Self {
        LinkedList { head: None, tail: None }
    }

    fn push_back(&mut self, value: T) {
        let new_tail = Box::new(Node {
            value,
            next: None,
            prev: self.tail,
        });

        let raw_tail: *mut Node<T> = Box::leak(new_tail);

        if let Some(mut tail) = self.tail {
            unsafe {
                (*tail).next = Some(raw_tail);
            }
        } else {
            self.head = Some(raw_tail);
        }

        self.tail = Some(raw_tail);
    }

    fn pop_back(&mut self) -> Option<T> {
        if let Some(tail) = self.tail.take() {
            unsafe {
                let node = Box::from_raw(tail);
                self.tail = node.prev;

                if let Some(mut prev) = node.prev {
                    (*prev).next = None;
                } else {
                    self.head = None;
                }

                Some(node.value)
            }
        } else {
            None
        }
    }
}

struct Stack<T> {
    list: LinkedList<T>,
}

impl<T> Stack<T> {
    fn new() -> Self {
        Stack { list: LinkedList::new() }
    }

    fn push(&mut self, value: T) {
        self.list.push_back(value);
    }

    fn pop(&mut self) -> Option<T> {
        self.list.pop_back()
    }

    fn is_empty(&self) -> bool {
        self.list.head.is_none()
    }

    fn peek(&self) -> Option<&T> {
        if let Some(tail) = self.list.tail {
            unsafe {
                Some(&(*tail).value)
            }
        } else {
            None
        }
    }
}
/* 
fn main() {
    let mut stack = Stack::new();

    stack.push(1);
    stack.push(2);
    stack.push(3);

    while let Some(value) = stack.pop() {
        println!("Popped: {}", value);
    }

    println!("Is the stack empty? {}", stack.is_empty());
}
*/
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stack_push_pop() {
        let mut stack = Stack::new();

        assert!(stack.is_empty());

        stack.push(1);
        stack.push(2);
        stack.push(3);

        assert_eq!(stack.pop(), Some(3));
        assert_eq!(stack.pop(), Some(2));
        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.pop(), None);

        assert!(stack.is_empty());
    }

    #[test]
    fn test_stack_peek() {
        let mut stack = Stack::new();

        assert_eq!(stack.peek(), None);

        stack.push(42);

        assert_eq!(stack.peek(), Some(&42));
        assert_eq!(stack.pop(), Some(42));
        assert_eq!(stack.peek(), None);
    }

    #[test]
    fn test_linked_list_push_pop() {
        let mut list = LinkedList::new();

        assert!(list.head.is_none());
        assert!(list.tail.is_none());

        list.push_back(1);
        list.push_back(2);
        list.push_back(3);

        assert_eq!(list.pop_back(), Some(3));
        assert_eq!(list.pop_back(), Some(2));
        assert_eq!(list.pop_back(), Some(1));
        assert_eq!(list.pop_back(), None);

        assert!(list.head.is_none());
        assert!(list.tail.is_none());
    }
}
