open Builtins
open OpCsp

let b = T.bool
let i = T.int
let f = T.make_fun_type
let t = T.make_tuple_type
let g = T.Gen 0
let g1 = T.Gen 1
let l t = T.App (T.List, [t])
let s t = T.App (T.Set, [t])

let builtin_fun_spec_list = [
    (id_not,         lognot,  f b b);
    (id_eq,          equal,   f g (f g b));
    (id_ne,          noteq,   f g (f g b));
    (id_lt,          lt,      f i (f i b));
    (id_gt,          gt,      f i (f i b));
    (id_le,          le,      f i (f i b));
    (id_ge,          ge,      f i (f i b));
    (id_neg,         neg,     f i i);
    (id_add,         add,     f i (f i i));
    (id_sub,         sub,     f i (f i i));
    (id_mul,         mul,     f i (f i i));
    (id_div,         div,     f i (f i i));
    (id_mod,         modulo,  f i (f i i));
    (Id.make "expt", expt,    f i (f i i));
    (* conversion *)
    (Id.make "set",  list_to_set,  f (l g) (s g));
    (Id.make "seq",  set_to_list,  f (s g) (l g));
    (* list *)
    (Id.make "null",         is_null,      f (l g) b);
    (Id.make "length",       length,       f (l g) i);
    (Id.make "head",         car,          f (l g) g);
    (Id.make "tail",         cdr,          f (l g) (l g));
    (Id.make "last",         last,         f (l g) g);
    (Id.make "butlast",      butlast,      f (l g) (l g));
    (Id.make "ref",          list_ref,     f (l g) (f i g));
    (Id.make "take",         take,         f (l g) (f i (l g)));
    (Id.make "drop",         drop,         f (l g) (f i (l g)));
    (Id.make "cons",         cons,         f g (f (l g) (l g)));
    (id_concat,              append,       f (l g) (f (l g) (l g)));
    (Id.make "update",       update,       f (l g) (f i (f g (l g))));
    (Id.make "remove1",      remove1,      f (l g) (f g (l g)));
    (Id.make "find_index",   find_index,   f (l g) (f g i));
    (Id.make "insert",       insert,       f (l g) (f i (f g (l g))));
    (Id.make "remove_index", remove_index, f (l g) (f i (l g)));
    (Id.make "reverse",      reverse,      f (l g) (l g));
    (Id.make "elem",         list_mem,     f g (f (l g) b));
    (Id.make "elim",         list_remove,  f (l g) (f g (l g)));
    (Id.make "interval",     interval,     f i (f i (l i)));
    (Id.make "repeat",       make_list,    f i (f g (l g)));
    (* set *)
    (Id.make "empty",        is_empty,     f (s g) b);
    (Id.make "subset",       is_subset,    f (s g) (f (s g) b));
    (Id.make "card",         card,         f (s g) i);
    (Id.make "adjoin",       adjoin,       f (s g) (f g (s g)));
    (Id.make "union",        union,        f (s g) (f (s g) (s g)));
    (Id.make "inter",        inter,        f (s g) (f (s g) (s g)));
    (Id.make "diff",         diff,         f (s g) (f (s g) (s g)));
    (Id.make "choice",       choice,       f (s g) g);
    (Id.make "member",       set_mem,      f g (f (s g) b));
    (Id.make "remove",       set_remove,   f (s g) (f g (s g)));

    (Id.make "map",          map,          f (f g g1) (f (l g) (l g1)));
    (Id.make "fold",         fold,         f (f g (f g1 g)) (f g (f (l g1) g)));
  ]
