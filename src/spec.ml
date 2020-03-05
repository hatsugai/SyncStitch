type variant_spec = {
    variant_name : Id.t;
    variant_type : T.t;
    ctor_spec_alist : (Id.t * ctor_spec) list;
    mutable variant_univ : V.t list;
  }

and ctor_spec = {
    ctor_name : Id.t;
    ctor_type_list : T.t list;
}

type channel_spec = {
    channel_name : Id.t;
    channel_type_list : T.t list;
    channel_domain : V.t list list;
  }

type process_spec = {
    process_name : Id.t;
    process_param_list : Id.t list;
    process_param_type_list : T.t list;
    process_expr : P.t;
  }

type fun_spec = {
    fun_name : Id.t;
    fun_param_list : Id.t list;
    fun_param_type_list : T.t list;
    fun_return_type : T.t;
    fun_expr : E.t;
  }

type builtin_fun_spec = {
    bf_name : Id.t;
    bf_fun : (V.t -> V.t list -> V.t) -> V.t list -> V.t;
    bf_type : T.t;
  }
