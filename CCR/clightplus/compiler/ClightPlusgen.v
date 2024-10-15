Require Import CoqlibCCR.
Require Import ITreelib.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import AList.

From compcert Require Import
     AST Maps Globalenvs Memory Values Linking Integers.
From compcert Require Import
     Ctypes Clight Clightdefs.

Require Import ClightPlusSkel.
Require Import ClightPlusExprgen.

Section HIDE.

  Definition hide (p: positive) {A: Type} {a: A} := a.
  Arguments hide _ {A} {a}: simpl never.

End HIDE.


Section Clight.
Context {eff : Type -> Type}.
Context {HasCall : callE -< eff}.
Context {HasEvent : eventE -< eff}.
Variable sk: Sk.t.
Let skenv: SkEnv.t := load_skenv sk.
Variable ce: comp_env.


Definition id_list_norepet_c: list ident -> bool :=
  fun ids => if Coqlib.list_norepet_dec (ident_eq) ids then true else false.

Definition id_list_disjoint_c: list ident -> list ident -> bool :=
  fun ids1 ids2 =>
    if (Coqlib.list_disjoint_dec ident_eq ids1 ids2)
    then true else false.

Fixpoint alloc_variables_c (ce: comp_env) (e: env)
         (vars: list (ident * type))
  : itree eff env :=
  match vars with
  | [] => Ret e
  | (id, ty) :: vars' =>
    b <- ccallU "salloc" (sizeof ce ty);;
    alloc_variables_c ce (alist_add id (b, ty) e) vars'
  end.

Definition function_entry_c
           (ce: comp_env) (f: function) (vargs: list val)
  : itree eff (env * temp_env) :=
  if (id_list_norepet_c (var_names (fn_vars f)) &&
      id_list_norepet_c (var_names (fn_params f)) &&
      id_list_disjoint_c (var_names (fn_params f))
                         (var_names (fn_temps f)))%bool
  then
    e <- alloc_variables_c ce [] (fn_vars f);;
    le <- (bind_parameter_temps (fn_params f) vargs (create_undef_temps (fn_temps f)))?;;
    Ret (e, le)
  else triggerUB.

Section DECOMP.

  Definition runtime_env : Type := env * temp_env * option bool * option val.

  Notation itr_t := (itree eff runtime_env).

  Definition _sassign_c e le a1 a2 :=
    tau;;
    vp <- eval_lvalue_c sk ce e le a1;;
    v <- eval_expr_c sk ce e le a2;;
    v' <- sem_cast_c v (typeof a2) (typeof a1);;
    assign_loc_c ce (typeof a1) vp v'.


  Definition _scall_c e le a al
    : itree eff val :=
    match Cop.classify_fun (typeof a) with
    | Cop.fun_case_f tyargs tyres cconv =>
      tau;;
      vf <- eval_expr_c sk ce e le a;;
      vargs <- eval_exprlist_c sk ce e le al tyargs;;
      match vf with
      | Vptr b ofs =>
          if Ptrofs.eq_dec ofs Ptrofs.zero
          then
            (* skeleton name = function name *)
            '(gsym, gd) <- (nth_error sk (pred (Pos.to_nat b)))?;;
            fd <- (match gd with Gfun fd => Some fd | _ => None end)?;;
            if type_eq (type_of_fundef fd) (Tfunction tyargs tyres cconv)
            then
              match fd with
              | Internal _
              (* malloc, free, capture's name in c level should equal to function name in ccr level *)
              | External EF_malloc _ _ _
              | External EF_free _ _ _
              | External EF_capture _ _ _ => ccallU gsym vargs
              (* this is for builtin memcpy, uncallable in standard C *)
              (* | EF_memcpy al sz => ccallU "memcpy" (al, sz, vargs) *)
              (* there's no system call currently *)
              | External _ _ _ _ => triggerUB
              end
            else triggerUB
          else triggerUB
      | _ => triggerUB
      end
    | _ => triggerUB
    end.

  Definition _site_c
             (e: env) (le: temp_env) (a: expr)
    : itree eff bool :=
    tau;;
    v1 <- eval_expr_c sk ce e le a;;
    bool_val_c v1 (typeof a).

  Definition sloop_iter_body_one
             (itr: itr_t)
    : itree eff (env * temp_env * (option (option val))) :=
    '(e', le', obc, v) <- itr;;
    match v with
    | Some retv =>
      (* return *)
      Ret (e', le', Some (Some retv))
    | None =>
        match obc with
        | None =>
        (* skip *)
        tau;;Ret (e', le', None)
        | Some true =>
        (* break, not return *)
        tau;;Ret (e', le', Some None)
        | Some false =>
        (* continue *)
        tau;;Ret (e', le', None)
        end
    end.

  Definition sloop_iter_body_two
             (itr: itr_t)
    : itree eff (env * temp_env * (option (option val))) :=
    '(e', le', obc, v) <- itr;;
    match v with
    | Some retv =>
      (* return *)
      Ret (e', le', Some (Some retv))
    | None =>
      match obc with
      | Some true => tau;;Ret (e', le', Some None)
      | Some false => triggerUB
      | None => tau;;Ret (e', le', None)
                (* this is for skip *)
      end
    end.

  Definition sloop_iter_body
             (itr1 itr2: env -> temp_env -> itr_t)
             (i: env * temp_env)
    : itree eff
            (env * temp_env +
             env * temp_env * option val) :=
    let '(e, le) := i in
    (* '(e1, le1, m1, obc1, v1) <- itr1 e le m ;; *)
    '(e1, le1, ov1) <- tau;;sloop_iter_body_one (itr1 e le) ;;
    match ov1 with
    | Some v1 =>
      (* break or return *)
      Ret (inr (e1, le1, v1))
    | None =>
      (* run loop2 *)
      '(e2, le2, ov2) <- sloop_iter_body_two (itr2 e1 le1);;
      match ov2 with
      | Some v2 =>
        Ret (inr (e2, le2, v2))
      | None =>
        Ret (inl (e2, le2))
      end
    end.

  Definition _sloop_itree (p: positive)
             (e: env) (le: temp_env)
             (itr1 itr2: positive -> env -> temp_env -> itr_t)
    : itr_t :=
    '(e', le', v) <-
    ITree.iter (@hide p _ (sloop_iter_body (itr1 (xO p)) (itr2 (xI p)))) (e, le) ;;
    Ret (e', le', None, v).

  Fixpoint free_list_aux (l: list (block * Z)): itree eff unit :=
    match l with
    | nil => Ret tt
    | (b, sz):: l' =>
      `_ : () <- ccallU "sfree" (Some b, sz);;
      free_list_aux l'
    end.

  Definition _sreturn_c
             (retty: type)
             (e: env) (le: temp_env)
             (oa: option expr)
    : itree eff val :=
    match oa with
    | None => tau;;Ret Vundef
    | Some a =>
      tau;;
      v <- eval_expr_c sk ce e le a;;
      sem_cast_c v (typeof a) retty
    end.

  Fixpoint decomp_stmt (p: positive)
           (retty: type)
           (stmt: statement)
    : env -> temp_env -> itr_t :=
    @hide p _
    (fun (e: env) (le: temp_env) =>
    match stmt with
    | Sskip =>
      Ret (e, le, None, None)
    | Sassign a1 a2 =>
      _sassign_c e le a1 a2;;;
      Ret (e, le, None, None)
    | Sset id a =>
      tau;;
      v <- eval_expr_c sk ce e le a ;;
      let le' := alist_add id v le in
      Ret (e, le', None, None)
    | Scall optid a al =>
        v <- _scall_c e le a al;;
        Ret (e, set_opttemp_alist optid v le, None, None)
    | Sbuiltin optid ef tyargs al =>
      tau;;
      vargs <- eval_exprlist_c sk ce e le al tyargs;;
        match ef with
        | EF_malloc => v <- ccallU "malloc" vargs;;
          Ret (e, set_opttemp_alist optid v le, None, None)
        | EF_free => v <- ccallU "free" vargs;;
          Ret (e, set_opttemp_alist optid v le, None, None)
        | EF_capture => v <- ccallU "capture" vargs;;
          Ret (e, set_opttemp_alist optid v le, None, None)
        (* this is for builtin memcpy, uncallable in standard C *)
        (* | EF_memcpy al sz => ccallU "memcpy" (al, sz, vargs) *)
        | _ => triggerUB
        end
    | Ssequence s1 s2 =>
      '(e', le', bc, v) <- tau;;decomp_stmt (xO p) retty s1 e le;;
                        (* this is for steps *)
      match v with
      | Some retval =>
        Ret (e', le', None, v)
      | None =>
        match bc with
        | None =>
          tau;;decomp_stmt (xI p) retty s2 e' le'
        | Some true =>
          tau;;Ret (e', le', bc, None)
        | Some false =>
          tau;;Ret (e', le', bc, None)
        end
      end
    | Sifthenelse a s1 s2 =>
      b <- _site_c e le a;;
      if (b: bool) then (decomp_stmt (xO p) retty s1 e le)
      else (decomp_stmt (xI p) retty s2 e le)
    | Sloop s1 s2 =>
      let itr1 := fun p => decomp_stmt p retty s1 in
      let itr2 := fun p => decomp_stmt p retty s2 in
      _sloop_itree (xO p) e le itr1 itr2
    | Sbreak =>
      Ret (e, le, Some true, None)
    | Scontinue =>
      Ret (e, le, Some false, None)
    | Sreturn oa =>
      v <- _sreturn_c retty e le oa;;
      Ret (e, le, None, Some v)
    | _ =>
      (* not supported *)
      triggerUB
    end).

  Definition decomp_func
           (f: Clight.function)
           (vargs: list val)
    : itree eff val :=
    '(e, le) <- function_entry_c ce (@hide (xO xH) _ f) vargs;;
    '(e', le', c, ov) <- decomp_stmt xH (fn_return f) (fn_body f) e le;;
    '(_, _, _, v) <- (match ov with
    | Some v => free_list_aux (blocks_of_env ce e');;; Ret (e', le', c, Some v)
    | None => match c : option bool with
              | Some b0 => if b0 then triggerUB else triggerUB
              | None => tau;; free_list_aux (blocks_of_env ce e');;; Ret (e', le', c, Some Vundef)
              end
    end);; v <- v?;;
    Ret v.

End DECOMP.
End Clight.
(* Notation call_data := (block * (* fundef * *) list val * mem)%type. *)

(* Section TRANS. *)

(*   (* Variable cprog_app: Clight.program. *) *)
(*   Variable global_definitions : list (ident * globdef fundef type). *)
(*   Variable public_idents : list ident. *)
(*   Let defined_names := List.map fst global_definitions. *)

(*   Fixpoint filter_dec_not {A: Type} {P: A -> Prop} (f: forall x: A, {P x} + {~ P x}) (l: list A) : list A := *)
(*     match l with *)
(*     | nil => nil *)
(*     | x :: l' => if f x then filter_dec_not f l' else x :: (filter_dec_not f l') *)
(*     end. *)

(*   Definition in_public x := in_dec Pos.eq_dec x public_idents. *)

(*   Definition rest_names := filter_dec_not in_public defined_names. *)

(*   Definition in_rest x := in_dec Pos.eq_dec x rest_names. *)

(*   Variable src_name : string.   (* source code file name *) *)

(*   Definition prefix_pos pos := ident_of_string (src_name ++ "." ++ (string_of_ident pos))%string. *)

(*   Definition rpl_pos pos := if in_rest pos then prefix_pos pos else pos. *)

(*   Definition rpl_glob := List.map (fun x => (rpl_pos (fst x), snd x)) global_definitions. *)

(*   Fixpoint rpl_expr (e: expr) := *)
(*     match e with *)
(*     | Econst_int _ _ | Econst_float _ _ | Econst_single _ _ *)
(*     | Econst_long _ _ | Etempvar _ _ | Esizeof _ _ | Ealignof _ _ => e *)
(*     | Evar id ty => Evar (rpl_pos id) ty *)
(*     | Ederef e' ty => Ederef (rpl_expr e') ty *)
(*     | Eaddrof e' ty => Eaddrof (rpl_expr e') ty *)
(*     | Eunop uop e' ty => Eunop uop (rpl_expr e') ty *)
(*     | Ebinop bop e1 e2 ty => Ebinop bop (rpl_expr e1) (rpl_expr e2) ty *)
(*     | Ecast e' ty => Ecast (rpl_expr e') ty *)
(*     | Efield e' id ty => Efield (rpl_expr e') id ty *)
(*     end. *)

(*   Fixpoint rpl_body (s : statement) := *)
(*     match s with *)
(*     | Sskip | Sbreak | Scontinue | Sgoto _ => s *)
(*     | Sassign a1 a2 => Sassign (rpl_expr a1) (rpl_expr a2) *)
(*     | Sset id a => Sset (rpl_pos id) (rpl_expr a) *)
(*     | Scall optid a al => *)
(*         Scall *)
(*           (option_rec (fun _ => _) (Some ∘ rpl_pos) None optid) *)
(*           (rpl_expr a) (List.map rpl_expr al) *)
(*     | Sbuiltin optid ef targs el => *)
(*         Sbuiltin *)
(*           (option_rec (fun _ => _) (Some ∘ rpl_pos) None optid) *)
(*           ef targs (List.map rpl_expr el) *)
(*     | Ssequence s1 s2 => Ssequence (rpl_body s1) (rpl_body s2) *)
(*     | Sifthenelse a s1 s2 => Sifthenelse (rpl_expr a) (rpl_body s1) (rpl_body s2) *)
(*     | Sloop s1 s2 => Sloop (rpl_body s1) (rpl_body s2) *)
(*     | Sreturn oa => Sreturn (option_rec (fun _ => _) (Some ∘ (rpl_expr)) None oa) *)
(*     | Sswitch a ls => Sswitch (rpl_expr a) (rpl_labeled_stmt ls) *)
(*     | Slabel l s => Slabel l (rpl_body s) *)
(*     end *)

(*   with rpl_labeled_stmt (ls: labeled_statements) := *)
(*          match ls with *)
(*          | LSnil => LSnil *)
(*          | LScons optz s ls' => LScons optz (rpl_body s) (rpl_labeled_stmt ls') *)
(*          end. *)

(*   Definition trans_func (f: function) := *)
(*     mkfunction f.(fn_return) f.(fn_callconv) f.(fn_params) f.(fn_vars) f.(fn_temps) (rpl_body f.(fn_body)). *)

(*   Definition trans_initval (ii : init_data) := *)
(*     match ii with *)
(*     | Init_addrof id ofs => Init_addrof (rpl_pos id) ofs *)
(*     | _ => ii *)
(*     end. *)

(*   Definition trans_var (gv: globvar type) := *)
(*     {| *)
(*       gvar_info := gv.(gvar_info); *)
(*       gvar_init := List.map trans_initval gv.(gvar_init); *)
(*       gvar_readonly := gv.(gvar_readonly); *)
(*       gvar_volatile := gv.(gvar_volatile); *)
(*     |} *)
(*   . *)

(*   Definition trans_global_def (g_def: globdef fundef type) := *)
(*     match g_def with *)
(*     | Gvar gv => Gvar (trans_var gv) *)
(*     | Gfun (Internal f) => Gfun (Internal (trans_func f)) *)
(*     | _ => g_def *)
(*     end. *)


(*   Definition trans_global_defs (g_defs: list (ident * globdef fundef type)) := *)
(*     List.map (fun x => (rpl_pos (fst x), trans_global_def (snd x))) g_defs. *)

(*   (* Program Definition append_srcname : Clight.program :=  *) *)
(*   (*   {| *) *)
(*   (*     prog_defs := trans_global_defs global_definitions; *) *)
(*   (*     prog_public := public_idents; *) *)
(*   (*     prog_main := cprog_app.(prog_main); *) *)
(*   (*     prog_types := cprog_app.(prog_types); *) *)
(*   (*     prog_comp_env := cprog_app.(prog_comp_env); *) *)
(*   (*   |}. *) *)
(*   (* Next Obligation. destruct cprog_app;auto. Qed. *) *)

(* End TRANS. *)

(* Section SITE_APP. *)
(*   (* for site specific execution *) *)
(*   (* not for proof *) *)
(*   Import EventsL. *)

(*   Definition sname := string. *)
(*   Variable sn: sname. *)
(*   Variable shared_fun_list: list gname. *)

(*   Let is_shared_fun fn := in_dec string_dec fn shared_fun_list. *)

(*   Definition site_append_morph_1 : Es ~> Es. (* for site specific module *) *)
(*   Proof. *)
(*     intros. destruct X. *)
(*     { destruct c. destruct (is_shared_fun fn). *)
(*       - exact (inl1 (Call mn fn args)). *)
(*       - exact (inl1 (Call mn (sn ++ "." ++ fn) args)). } *)
(*     destruct s. *)
(*     { destruct s. *)
(*       { destruct (is_shared_fun fn). *)
(*         - exact (inr1 (inl1 (Spawn fn args))). *)
(*         - exact (inr1 (inl1 (Spawn (sn ++ "." ++ fn) args))). } *)
(*       exact (inr1 (inl1 Yield)). *)
(*       exact (inr1 (inl1 Getpid)). *)
(*       exact (inr1 (inl1 Getsn)). } *)
(*     destruct s. *)
(*     { destruct p. *)
(*       - exact (inr1 (inr1 (inl1 (PPut (sn ++ "." ++ mn) p)))). *)
(*       - exact (inr1 (inr1 (inl1 (PGet (sn ++ "." ++ mn))))). } *)
(*     { destruct e. *)
(*       exact (inr1 (inr1 (inr1 (Choose X)))). *)
(*       exact (inr1 (inr1 (inr1 (Take X)))). *)
(*       exact (inr1 (inr1 (inr1 (Syscall fn args rvs)))). } *)
(*   Defined. *)

(*   Definition site_append_morph_2 (sn': sname) : Es ~> Es. (* for shared module *) *)
(*   Proof. *)
(*     intros. destruct X. *)
(*     { destruct c. destruct (is_shared_fun fn). *)
(*       - exact (inl1 (Call mn fn args)). *)
(*       - exact (inl1 (Call mn (sn' ++ "." ++ fn) args)). } *)
(*     destruct s. *)
(*     { destruct s. *)
(*       { destruct (is_shared_fun fn). *)
(*         - exact (inr1 (inl1 (Spawn fn args))). *)
(*         - exact (inr1 (inl1 (Spawn (sn' ++ "." ++ fn) args))). } *)
(*       exact (inr1 (inl1 Yield)). *)
(*       exact (inr1 (inl1 Getpid)). *)
(*       exact (inr1 (inl1 Getsn)). *)
(*     } *)
(*     destruct s. *)
(*     { destruct p. *)
(*       - exact (inr1 (inr1 (inl1 (PPut mn p)))). *)
(*       - exact (inr1 (inr1 (inl1 (PGet mn)))). } *)
(*     { destruct e. *)
(*       exact (inr1 (inr1 (inr1 (Choose X)))). *)
(*       exact (inr1 (inr1 (inr1 (Take X)))). *)
(*       exact (inr1 (inr1 (inr1 (Syscall fn args rvs)))). } *)
(*   Defined. *)


(*   Definition site_appended_itree_1 : itree Es ~> itree Es := translate site_append_morph_1. *)
(*   Definition site_appended_itree_2 (sn': sname) : itree Es ~> itree Es := translate (site_append_morph_2 sn'). *)

(*   Definition append_site_1 (ms: ModSemL.t) : ModSemL.t := *)
(*     {| *)
(*       ModSemL.fnsems := List.map (fun '(gn, fnsem) => *)
(*                        ((sn ++ "." ++ gn)%string, fun x => site_appended_itree_1 _ (fnsem x))) ms.(ModSemL.fnsems); *)
(*       ModSemL.initial_mrs := List.map (map_fst (fun mn => (sn ++ "." ++ mn)%string)) ms.(ModSemL.initial_mrs); *)
(*     |} *)
(*   . *)

(*   Definition append_caller_site {X Y: Type} (body: X -> itree Es Y) := *)
(*     fun x => sn' <- trigger Getsn;; site_appended_itree_2 sn' _ (body x). *)

(*   Definition append_site_2 (ms: ModSemL.t) : ModSemL.t := *)
(*     {| *)
(*       ModSemL.fnsems := List.map *)
(*                           (fun '(gn, fnsem) => (gn, append_caller_site fnsem)) ms.(ModSemL.fnsems); *)
(*       ModSemL.initial_mrs := ms.(ModSemL.initial_mrs); *)
(*     |} *)
(*   . *)

(* End SITE_APP. *)

From compcert Require Import Errors.

Section DECOMP_PROG.

  Definition get_ce (prog: Clight.program) : comp_env := PTree.elements prog.(prog_comp_env).

  Variable prog: Clight.program.
  Let ce: comp_env := get_ce prog.
  Let defs: list (ident * globdef Clight.fundef type) := prog.(prog_defs).
  Let public: list ident := prog.(prog_public).
  Variable mn: string.

  (* Fixpoint get_source_name (filename : string) := *)
  (* String.substring 0 (String.length filename - 2) filename. *)

  (* local compilation condition *)
  Definition def_filter (gdef: ident * globdef Clight.fundef type) : bool :=
    match gdef with
    | (_, Gvar _) | (_, Gfun (Internal _)) => true
    | _ => false
    end.

  Definition chk_ident (name: ident) : bool := Pos.eq_dec name (ident_of_string (string_of_ident name)).

  Definition chk_init_data (i: init_data) : bool :=
    match i with
    | Init_addrof symb _ => chk_ident symb
    | _ => true
    end.

  Definition chk_gd (gd: globdef Clight.fundef type) : bool :=
    match gd with
    | Gvar (mkglobvar _ il _ _) => forallb chk_init_data il
    | _ => true
    end.

  Definition main_type ident fd : bool :=
    if Pos.eq_dec ident (ident_of_string "main")
    then type_eq (type_of_fundef fd) (Tfunction Ctypes.Tnil type_int32s cc_default)
    else true.

  Definition call_ban (entry: ident * globdef Clight.fundef type) : bool :=
    let (ident, gd) := entry in
    match gd with
    | Gfun (External EF_malloc _ _ _) => Pos.eq_dec ident (ident_of_string "malloc")
    | Gfun (External EF_free _ _ _) => Pos.eq_dec ident (ident_of_string "free")
    | Gfun (External EF_capture _ _ _) => Pos.eq_dec ident (ident_of_string "capture")
    | Gfun fd => negb (in_dec Pos.eq_dec ident [ident_of_string "malloc"; ident_of_string "free"; ident_of_string "capture"; ident_of_string "salloc"; ident_of_string "sfree";ident_of_string "load";ident_of_string "store";ident_of_string "sub_ptr";ident_of_string "cmp_ptr";ident_of_string "non_null?";ident_of_string "memcpy"]) && main_type ident fd
    | _ => negb (in_dec Pos.eq_dec ident [ident_of_string "malloc"; ident_of_string "free"; ident_of_string "capture"; ident_of_string "salloc"; ident_of_string "sfree";ident_of_string "load";ident_of_string "store";ident_of_string "sub_ptr";ident_of_string "cmp_ptr";ident_of_string "non_null?";ident_of_string "memcpy"])
    end.

  Definition get_sk (defs: list (ident * globdef Clight.fundef type)) : res Sk.t :=
    if Coqlib.list_norepet_dec dec (List.map fst defs) && (forallb call_ban defs)
    then
      let sk := List.filter def_filter defs in
      if List.forallb chk_ident (List.map fst sk) && forallb chk_gd (List.map snd sk)
      then OK (List.map (map_fst string_of_ident) sk)
      else Error [MSG "failed in gdchk"]
    else Error [MSG "failed in norepet"].

  Fixpoint get_fnsems (sk: Sk.t) (defs: list (string * globdef Clight.fundef type)) : list (string * (option string * Any.t -> itree Es Any.t)) :=
    match defs with
    | [] => []
    | (gn, Gfun (Internal f)) :: defs' => (gn, cfunU (decomp_func sk ce f)) :: get_fnsems sk defs'
    | _ :: defs' => get_fnsems sk defs'
    end.

  Definition compile : res Mod.t :=
    if Pos.eq_dec (prog_main prog) (ident_of_string "main")
    then
      match get_sk defs with
      | OK _sk =>
        OK {| Mod.get_modsem := fun sk => {| ModSem.fnsems := get_fnsems sk _sk; ModSem.mn := mn; ModSem.initial_st := tt↑; |};
              Mod.sk := _sk; |}
      | Error msgs => Error msgs
      end
    else Error [MSG "entry point is not main"].

  (* global compilation condition *)
  Require Import ClightPlusMem0.

  Definition mem_keywords := List.map ident_of_string ["malloc"; "free"; "capture"]%string.

  Definition mem_init_cond (sk sk': Sk.t) := forall s v, In (s, Gvar v) sk -> Genv.init_data_list_aligned 0 (gvar_init v) /\ (forall symb ofs, In (Init_addrof symb ofs) (gvar_init v) -> exists idx, SkEnv.id2blk (load_skenv sk') (string_of_ident symb) = Some idx).

  Definition init_data_list_aligned_dec il p : { Genv.init_data_list_aligned p il} + { ~ Genv.init_data_list_aligned p il}.
  Proof.
    revert p. induction il; ss; et. i. destruct (IHil (p + init_data_size a)%Z); cycle 1. { right. ii. apply n. des. et. }
    destruct (Zdivide_dec (Genv.init_data_alignment a) p). { left. et. } right. ii. apply n. des. et.
  Qed.

  Definition addr_find_dec sk il : { forall symb ofs, In (Init_addrof symb ofs) il -> exists idx, SkEnv.id2blk (load_skenv sk) (string_of_ident symb) = Some idx } + {~ (forall symb ofs, In (Init_addrof symb ofs) il -> exists idx, SkEnv.id2blk (load_skenv sk) (string_of_ident symb) = Some idx) }.
  Proof.
    induction il; ss. { left. i. clarify. }
    destruct IHil; cycle 1.
    - right. ii. apply n. i. et.
    - destruct a.
      all: try solve [left; ii; des; clarify; et].
      destruct (SkEnv.id2blk (load_skenv sk) (string_of_ident i)) eqn:?.
      + left. i. des; et. clarify. et.
      + right. ii. hexploit H; et. i. des. clarify.
  Qed.

  Definition mem_init_cond_dec sk sk' : { mem_init_cond sk sk'} + { ~ mem_init_cond sk sk'}.
  Proof.
    revert sk'. induction sk; i. { left. ss. }
    destruct (IHsk sk'); cycle 1.
    - right. ii. apply n. ii. red in H. hexploit H; et. ss. et.
    - destruct a. destruct g.
      + left. ii. red in m. ss. des; et. clarify.
      + destruct (init_data_list_aligned_dec (gvar_init v) 0); cycle 1.
        { right. ii. apply n. red in H. hexploit H; et. { ss. et. } i. des. et. }
        destruct (addr_find_dec sk' (gvar_init v)).
        { left. ii. ss. des; et. clarify. }
        right. ii. red in H. hexploit H; et. { ss. et. } i. des. et.
  Defined.

  Definition mem_skel : res Sk.t :=
    match get_sk defs with
    | OK sk =>
      let sk_mem := List.map (map_fst string_of_ident) (List.filter (fun x => in_dec Pos.eq_dec (fst x) mem_keywords) defs) in
      match mem_init_cond_dec (Sk.canon (Sk.add sk_mem sk)) (Sk.canon (Sk.add sk_mem sk)) with
      | in_left => OK sk_mem
      | in_right => Error [MSG "memory initialization failed"]
      end
    | Error msgs => Error msgs
    end.

End DECOMP_PROG.
Global Opaque mem_init_cond_dec.

(* Section EXECUTION_STRUCTURE. *)
(*   (*   execution modules consist of modules executes in sites independently  *) *)
(*   (*   and modules accessable in every sites. *) *)
(*   (* ------------------------------------------------------------------------ *) *)
(*   (* example *) *)
(*   (* site A : A1 A2 A3 *) *)
(*   (* site B : B1 B2 B3 *) *)
(*   (* shared : C1 C2 C3 *) *)
(*   (* f: function append site name in local state and its own function *) *)
(*   (* g: function append current site name in site specific function (so, its site name dynamically determined) *) *)
(*   (* A's ModSemL: f (MemA + A1 + A2 + A3) <_ (enclose) skel of site A and shared *) *)
(*   (* B's ModSemL: f (MemB + B1 + B2 + B3) <_ (enclose) skel of site B and shared *) *)
(*   (* shared's ModSemL: g (C1 + C2 + C3) <_(enclose) skel of site A and site B and shared *) *)

(*   Fixpoint remove_mult_name (l : Sk.t) : Sk.t := *)
(*     match l with *)
(*       | [] => [] *)
(*       | (gn, gd)::xs => if in_dec string_dec gn (List.map fst xs) then remove_mult_name xs else (gn, gd)::(remove_mult_name xs) *)
(*     end. *)

(*   (* for skeleton padding *) *)
(*   Definition sk_padmod (sk: Sk.t) := ModL.mk ModL.empty.(ModL.get_modsem) sk. *)

(*   (* get one site's ModSemL *) *)
(*   Definition proc_gen (shared_module: ModL.t) : sname * list Mod.t -> ModSemL.t := *)
(*     fun '(sn, modlist) => *)
(*       (append_site_1 sn (List.map fst shared_module.(ModL.enclose).(ModSemL.fnsems)) *)
(*          (ModL.enclose (ModL.add (Mod.add_list modlist) (sk_padmod shared_module.(ModL.sk))))). *)

(*   (* turns exec_profile into one ModSemL *) *)
(*   Definition sum_of_site_modules_view (exec_profile: list (sname * list Mod.t)) (shared_module: ModL.t) : ModSemL.t := *)
(*     List.fold_left ModSemL.add (List.map (proc_gen shared_module) exec_profile) (ModSemL.mk [] []). *)

(*   (* get all skeletons in sites and concat *) *)
(*   Definition sum_of_site_skeletons (exec_profile: list (sname * list Mod.t)) : Sk.t := *)
(*       remove_mult_name (List.concat (List.map (fun '(sn, modlist) => (Mod.add_list modlist).(ModL.sk)) exec_profile)). *)

(*   (* turn shared modules into one ModSemL *) *)
(*   Definition view_shared_module (exec_profile: list (sname * list Mod.t)) (shared_module: ModL.t) : ModSemL.t := *)
(*     append_site_2 (List.map fst shared_module.(ModL.enclose).(ModSemL.fnsems)) *)
(*       (ModL.enclose (ModL.add shared_module (sk_padmod (sum_of_site_skeletons exec_profile)))). *)

(* End EXECUTION_STRUCTURE. *)
