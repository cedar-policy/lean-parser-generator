//! The arena and the arena list used by `rustarena.lig` (`%option rust_ctx`, `%option rust_list`).

/// The `ctx` of `parse_values`: every node of the Rust AST is allocated in it.
pub type Arena = bumpalo::Bump;

pub mod lists {
    use super::Arena;

    /// A cell of a singly linked list that lives in the arena.
    pub struct Cons<'a, T> {
        pub head: T,
        pub tail: List<'a, T>,
    }

    /// The list type of the macro rules (`separated_list`, …): `nil`, `one` and `cons` build it.
    pub struct List<'a, T>(pub Option<&'a Cons<'a, T>>);

    impl<'a, T> Clone for List<'a, T> {
        fn clone(&self) -> Self {
            *self
        }
    }
    impl<'a, T> Copy for List<'a, T> {}

    impl<'a, T> List<'a, T> {
        pub fn iter(&self) -> Iter<'a, T> {
            Iter(self.0)
        }
    }

    pub struct Iter<'a, T>(Option<&'a Cons<'a, T>>);

    impl<'a, T> Iterator for Iter<'a, T> {
        type Item = &'a T;
        fn next(&mut self) -> Option<&'a T> {
            let c = self.0?;
            self.0 = c.tail.0;
            Some(&c.head)
        }
    }

    impl<'a, T: std::fmt::Debug> std::fmt::Debug for List<'a, T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_list().entries(self.iter()).finish()
        }
    }

    impl<'a, T: PartialEq> PartialEq for List<'a, T> {
        fn eq(&self, other: &Self) -> bool {
            self.iter().eq(other.iter())
        }
    }

    pub fn nil<'a, T>(_ctx: &'a Arena) -> List<'a, T> {
        List(None)
    }

    pub fn one<'a, T>(ctx: &'a Arena, x: T) -> List<'a, T> {
        List(Some(ctx.alloc(Cons { head: x, tail: List(None) })))
    }

    pub fn cons<'a, T>(ctx: &'a Arena, x: T, xs: List<'a, T>) -> List<'a, T> {
        List(Some(ctx.alloc(Cons { head: x, tail: xs })))
    }
}
