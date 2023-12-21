interface LinkedList
    exposes [
        LinkedList,
        single,
        push,
        pop,
        toList,
        fromList,
        concat,
        walk,
        empty,
        len,
    ]
    imports []

LinkedList a := LL a implements [Eq, Hash]

LL a : [Nil, Cons { first : a, rest : LL a, length : Nat }]

empty : {} -> LinkedList a
empty = \{} -> @LinkedList Nil

len : LinkedList a -> Nat
len = \@LinkedList list ->
    when list is
        Nil -> 0
        Cons { length } -> length

single : a -> LinkedList a
single = \item -> @LinkedList (Cons { first: item, rest: Nil, length: 1 })

push : LinkedList a, a -> LinkedList a
push = \@LinkedList list, item -> @LinkedList (Cons { first: item, rest: list, length: (len (@LinkedList list)) + 1 })

pop : LinkedList a -> [Cons { first : a, rest : LinkedList a }, Nil]
pop = \@LinkedList list ->
    when list is
        Nil -> Nil
        Cons { first, rest } -> Cons { first, rest: @LinkedList rest }

toList : LinkedList a -> List a
toList = \linkedList ->
    walk linkedList (List.withCapacity (len linkedList)) \state, elem ->
        List.append state elem

fromList : List a -> LinkedList a
fromList = \list ->
    List.walkBackwards list (LinkedList.empty {}) \accum, elem -> LinkedList.push accum elem

concat : LinkedList a, LinkedList a -> LinkedList a
concat = \@LinkedList list1, @LinkedList list2 ->
    concatenated =
        when list1 is
            Nil -> list2
            Cons { first, rest, length } ->
                Cons {
                    first: first,
                    rest: concat (@LinkedList rest) (@LinkedList list2),
                    length: (len (@LinkedList list2)) + length,
                }
    @LinkedList concatenated

walk : LinkedList elem, state, (state, elem -> state) -> state
walk = \@LinkedList list, state, fn ->
    when list is
        Nil -> state
        Cons { first, rest } -> walk (@LinkedList rest) (fn state first) fn

expect fromList ([1, 2, 3]) == push (push (single 3) 2) 1
expect fromList [] == empty {}
expect toList (push (push (single 3) 2) 1) == [1, 2, 3]
expect toList (empty {}) == []
expect pop (empty {}) == Nil
expect concat (push (push (single 3) 2) 1) (empty {}) == (push (push (single 3) 2) 1)
expect concat (push (push (single 3) 2) 1) (push (push (single 6) 5) 4) == (push (push (push (push (push (single 6) 5) 4) 3) 2) 1)
expect len (push (push (single 3) 2) 1) == 3
expect len (single 0) == 1
expect len (empty {}) == 0
expect pop (push (push (single 3) 2) 1) == Cons { first: 1, rest: push (single 3) 2 }
expect pop (single 0) == Cons { first: 0, rest: empty {} }
expect pop (empty {}) == Nil
