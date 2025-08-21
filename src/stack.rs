// Simple stack implementation using fixed-size array for no_std compatibility
#[allow(dead_code)]
const STACK_SIZE: usize = 1000;

#[allow(dead_code)]
pub struct Stack<T: Copy + Default> {
    data: [T; STACK_SIZE],
    len: usize,
}

#[allow(dead_code)]
impl<T: Copy + Default> Stack<T> {
    pub fn new() -> Self {
        Stack {
            data: [T::default(); STACK_SIZE],
            len: 0,
        }
    }

    pub fn push(&mut self, value: T) -> Result<(), &'static str> {
        if self.len >= STACK_SIZE {
            Err("Stack overflow")
        } else {
            self.data[self.len] = value;
            self.len += 1;
            Ok(())
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            Some(self.data[self.len])
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn peek(&self) -> Option<&T> {
        if self.len == 0 {
            None
        } else {
            Some(&self.data[self.len - 1])
        }
    }

    pub fn len(&self) -> usize {
        self.len
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
        let mut stack: Stack<i32> = Stack::new();

        assert!(stack.is_empty());

        stack.push(1).unwrap();
        stack.push(2).unwrap();
        stack.push(3).unwrap();

        assert_eq!(stack.pop(), Some(3));
        assert_eq!(stack.pop(), Some(2));
        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.pop(), None);

        assert!(stack.is_empty());
    }

    #[test]
    fn test_stack_peek() {
        let mut stack: Stack<i32> = Stack::new();

        assert_eq!(stack.peek(), None);

        stack.push(42).unwrap();

        assert_eq!(stack.peek(), Some(&42));
        assert_eq!(stack.pop(), Some(42));
        assert_eq!(stack.peek(), None);
    }

    #[test]
    fn test_stack_len() {
        let mut stack: Stack<i32> = Stack::new();

        assert_eq!(stack.len(), 0);

        stack.push(1).unwrap();
        assert_eq!(stack.len(), 1);

        stack.push(2).unwrap();
        assert_eq!(stack.len(), 2);

        stack.pop();
        assert_eq!(stack.len(), 1);

        stack.pop();
        assert_eq!(stack.len(), 0);
    }
}
