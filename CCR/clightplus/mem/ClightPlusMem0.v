Require Import CoqlibCCR.
Require Import ITreelib.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import AList.
Require Import ClightPlusSkel.

From compcert Require Import
     AST Maps Globalenvs Memory Values IntPtrRel Linking Integers.
From compcert Require Import
     Ctypes Clight Clightdefs.
Import Clightdefs.ClightNotations.

Set Implicit Arguments.


Section MODSEM.
  Local Open Scope Z.
  Variable sk: Sk.t.
  Let skenv: SkEnv.t := load_skenv sk.

  Section BODY.
    Context `{has_pE: pE -< Es}.
    Context `{has_eventE: eventE -< Es}.
    Context `{has_callE: callE -< Es}.

    (* stack allocation of memory *)
    Definition sallocF: Z -> itree Es block :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let (m1, blk) := Mem.alloc m0 0 varg in
        trigger (PPut m1↑);;;
        Ret blk.

    Definition sfreeF: option block * Z -> itree Es unit :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(ob, sz) := varg in
        match ob with
        | Some b => m1 <- (Mem.free m0 b 0 sz)?;;
                   trigger (PPut m1↑);;;
                   Ret tt
        | None => triggerUB
        end
    .

    (* corresponds to Mem.loadv *)
    Definition loadF: memory_chunk * val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(chunk, addr) := varg in
        v <- (Mem.loadv chunk m0 addr)?;;
        Ret v
    .

  (* deprecated, maybe revive in bitfield at v3.11? *)
    (* Definition loadbytesF: val * Z -> itree Es (list memval) :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(addr, n) := varg in
        match addr with
        | Vptr b ofs =>
            v <- (Mem.loadbytes m0 b (Ptrofs.unsigned ofs) n)?;;
            Ret v
        | _ => triggerUB
        end
    . *)

    (* corresponds to Mem.storev *)
    Definition storeF: memory_chunk * val * val -> itree Es unit :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(chunk, addr, v) := varg in
        m1 <- (Mem.storev chunk m0 addr v)?;;
        trigger (PPut m1↑);;;
        Ret tt
    .

  (* deprecated, maybe revive in bitfield at v3.11? *)
    (* Definition storebytesF: val * list memval -> itree Es unit :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        let '(addr, bytes) := varg in
        match addr with
        | Vptr b ofs =>
            m1 <- (Mem.storebytes m0 b (Ptrofs.unsigned ofs) bytes)?;;
            trigger (PPut m1↑);;;
            Ret tt
        | _ => triggerUB
        end
    . *)

    (* corresponds to Cop.cmp_ptr_join_common *)
    Definition cmp_ptrF : comparison * val * val -> itree Es bool :=
      fun varg =>
        mp <- trigger PGet;;
        m <- mp↓?;;
        let '(c, v1, v2) := varg in
        if Archi.ptr64
        then (cmplu_join_common m c v1 v2)?
        else (cmpu_join_common m c v1 v2)?.

    Definition sub_ptrF : Z * val * val -> itree Es val :=
      fun varg =>
        let '(sz, v1, v2) := varg in
          mp <- trigger (PGet);;
          m <- mp↓?;;
          n <- (Cop._sem_ptr_sub_join_common v1 v2 m)?;;
          if Coqlib.proj_sumbool (Coqlib.zlt 0 sz) &&
               Coqlib.proj_sumbool (Coqlib.zle sz Ptrofs.max_signed)
          then Ret (Vptrofs (Ptrofs.divs n (Ptrofs.repr sz)))
          else triggerUB.

    Definition non_nullF: val -> itree Es bool :=
      fun varg =>
        mp <- trigger (PGet);;
        m <- mp↓?;;
        match varg with
        | Vptr b ofs =>
          if (Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs)) then Ret true
          else triggerUB
        (* unreachable case in clightplus *)
        | Vlong i => if Archi.ptr64 then Ret (Int64.cmpu Cne Int64.zero i) else triggerUB
        | Vint i => if negb Archi.ptr64 then Ret (Int.cmpu Cne Int.zero i) else triggerUB
        | _ => triggerUB
        end
    .

    Definition mallocF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(m1, b) <- (match Archi.ptr64, varg with
                    | true, [Vlong i] =>
                        Ret (Mem.alloc m0 (- size_chunk Mptr) (Int64.unsigned i))
                    | false, [Vint i] =>
                        Ret (Mem.alloc m0 (- size_chunk Mptr) (Int.unsigned i))
                    | _, _ => triggerUB
                    end);;
        v <- (hd_error varg)?;;
        m2 <- (Mem.store Mptr m1 b (- size_chunk Mptr) v)?;;
        trigger (PPut m2↑);;;
        Ret (Vptr b Ptrofs.zero)
    .

    Definition mfreeF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        `b: bool <- (match Archi.ptr64, varg with
                    | true, [Vlong i] => if Int64.eq i Int64.zero then Ret true else Ret false
                    | false, [Vint i] => if Int.eq i Int.zero then Ret true else Ret false
                    | _, [_] => Ret false
                    | _, _ => triggerUB
                    end);;
        if b then Ret Vundef
        else
          match varg with
          | [vaddr] =>
            match Mem.to_ptr vaddr m0 with
            | Some (Vptr b ofs) =>
              v_sz <- (Mem.load Mptr m0 b (Ptrofs.unsigned ofs - size_chunk Mptr))?;;
              let sz := match Archi.ptr64, v_sz with
                        | true, Vlong i => Int64.unsigned i
                        | false, Vint i => Int.unsigned i
                        (* unreachable *)
                        | _, _ => - 1
                        end in
              if Coqlib.zlt 0 sz
              then m1 <- (Mem.free m0 b (Ptrofs.unsigned ofs - size_chunk Mptr) (Ptrofs.unsigned ofs + sz))?;;
                  trigger (PPut m1↑);;;
                  Ret Vundef
              else triggerUB
            | _ => triggerUB
            end
          | _ => triggerUB
          end
    .

    Definition memcpyF: Z * Z * list val -> itree Es val :=
      fun varg =>
        let '(al, sz, vl) := varg in
        match vl with
        | [vaddr; vaddr'] =>
          if dec sz 0 then Ret Vundef
          else
            mp <- trigger (PGet);;
            m <- mp↓?;;
            vp <- (Mem.to_ptr vaddr m)?;;
            vp' <- (Mem.to_ptr vaddr' m)?;;
            match vp, vp' with
            | Vptr b ofs, Vptr b' ofs' =>
              let chk1 := dec al 1 || dec al 2 || dec al 4 || dec al 8 in
              let chk2 := Coqlib.zle 0 sz && Zdivide_dec al sz in
              let chk3 := Zdivide_dec al (Ptrofs.unsigned ofs') && Zdivide_dec al (Ptrofs.unsigned ofs) in
              if negb (chk1 && chk2 && chk3) then triggerUB
              else
                let odst := Ptrofs.unsigned ofs in
                let osrc := Ptrofs.unsigned ofs' in
                let chk4 := Coqlib.zle (osrc + sz) odst || Coqlib.zle (odst + sz) osrc || negb (dec b' b) || dec odst osrc in
                if negb chk4 then triggerUB
                else bytes <- (Mem.loadbytes m b' osrc sz)?;;
                     m' <- (Mem.storebytes m b odst bytes)?;;
                     trigger (PPut m'↑);;; Ret Vundef
            | _, _ => triggerUB
            end
        | _ => triggerUB
        end.

    Definition captureF : list val -> itree Es val :=
      fun varg =>
        mp <- trigger (PGet);;
        m <- mp↓?;;
        match varg with
        | [Vptr b ofs] =>
          if negb (Coqlib.plt b m.(Mem.nextblock)) then triggerUB
          else
            '(exist (i, m') _) <- trigger (Choose { im' : Z * mem | Mem.capture m b (fst im') (snd im')});;
            trigger (PPut m'↑);;;
            Ret (Vptrofs (Ptrofs.repr (i + Ptrofs.unsigned ofs)))
        | [Vint i] => if Archi.ptr64 then triggerUB else Ret (Vint i)
        | [Vlong i] => if Archi.ptr64 then Ret (Vlong i) else triggerUB
        | _ => triggerUB
        end.

    (* Definition reallocF: list val -> itree Es val :=
      fun varg =>
        match varg with
        | [addr;v_sz'] =>
            match Archi.ptr64, addr with
            | true, Vlong (Int64.mkint 0 _)
            | false, Vint (Int.mkint 0 _) => ccallU "malloc" [v_sz']
            | _, Vptr b ofs =>
                (* Read the size of the allocated memory *)
                mp0 <- trigger (PGet);;
                m0 <- mp0↓?;;
                v_sz <- (Mem.load Mptr m0 b (Ptrofs.unsigned ofs - size_chunk Mptr)%Z)?;;
                let sz := match Archi.ptr64, v_sz with
                      | true, Vlong i =>
                          Int64.unsigned i
                      | false, Vint i =>
                          Int.unsigned i
                      | _, _ => (- 1)%Z
                      end in
                let sz' := match Archi.ptr64, v_sz' with
                      | true, Vlong i =>
                          Int64.unsigned i
                      | false, Vint i =>
                          Int.unsigned i
                      | _, _ => (- 1)%Z
                      end in
                if (sz >=? 0)%Z && (sz' >=? 0)%Z
                then
                    (* if (sz >=? sz')%Z then (* Reducing the size of the allocated memory *) *)
                    (*      `_: () <- ccallU "free" (b, sz', sz);; *)
                    (*          `_: () <- ccallU "store" (Mptr, b, (- size_chunk Mptr)%Z, Vlong (Int64.repr sz'));; *)
                    (*          Ret (Vptr b (Ptrofs.repr ofs)) *)
                    (*    else (* Increasing the size of the allocated memory *) *)
                    `addr': val <- ccallU "malloc" [v_sz'];;
                    `data: list memval <- ccallU "loadbytes" (addr, sz);;
                    `_: () <- ccallU "free" [addr];;
                    `_: () <- ccallU "storebytes" (addr', firstn (Z.to_nat sz') data);;
                    Ret addr'
                else triggerUB (* Behaviours vary depending on implementations *)
            | _, _ => triggerUB
            end
        | _ => triggerUB
        end. *)

  End BODY.

  Section STATE.

  Definition store_init_data (m : mem) (b : block) (p : Z) (id : init_data) :=
    match id with
    | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
    | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
    | Init_int32 n => Mem.store Mint32 m b p (Vint n)
    | Init_int64 n => Mem.store Mint64 m b p (Vlong n)
    | Init_float32 n => Mem.store Mfloat32 m b p (Vsingle n)
    | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
    | Init_space _ => Some m
    | Init_addrof symb ofs =>
        match SkEnv.id2blk skenv (string_of_ident symb) with
        | Some b' => Mem.store Mptr m b p (Vptr (Pos.of_succ_nat b') ofs)
        | None => None
        end
    end.

  Fixpoint store_init_data_list (m : mem) (b : block) (p : Z) (idl : list init_data) {struct idl} : option mem :=
    match idl with
    | [] => Some m
    | id :: idl' =>
        match store_init_data m b p id with
        | Some m' => store_init_data_list m' b (p + init_data_size id)%Z idl'
        | None => None
        end
    end.

  Definition alloc_global (m : mem) (gd : globdef fundef type) : option mem :=
    match gd with
    | Gfun _ => let (m1, b) := Mem.alloc m 0 1 in Mem.drop_perm m1 b 0 1 Nonempty
    | Gvar v =>
      let init := gvar_init v in
      let sz := init_data_list_size init in
      let (m1, b) := Mem.alloc m 0 sz in
      match store_zeros m1 b 0 sz with
      | Some m2 =>
          match store_init_data_list m2 b 0 init with
          | Some m3 => Mem.drop_perm m3 b 0 sz (Genv.perm_globvar v)
          | None => None
          end
      | None => None
      end
    end.

  Fixpoint alloc_globals (m: mem) (sk: Sk.t) : option mem :=
    match sk with
    | nil => Some m
    | g :: gl' =>
      let (_, gd) := g in
      match alloc_global m gd with
      | Some m' => alloc_globals m' gl'
      | None => None
      end
    end.

  Definition load_mem := alloc_globals Mem.empty sk.

  Definition default_mem : mem.
  Proof.
    destruct Mem.empty. unfold block in *.
    eapply (Mem.mkmem mem_contents mem_access mem_concrete (Pos.add nextblock (Pos.of_nat (List.length sk)))); et.
    - i. apply nextblock_noaccess. unfold Coqlib.Plt in *. nia.
    - i. apply nextblocks_logical. unfold Coqlib.Plt in *. nia.
  Defined.

  End STATE.


  Definition MemSem : ModSem.t :=
      {|
        ModSem.fnsems := [("salloc", cfunU sallocF); ("sfree", cfunU sfreeF);
                          ("load", cfunU loadF);
                          (* ("loadbytes", cfunU loadbytesF); *)
                          ("store", cfunU storeF);
                          (* ("storebytes", cfunU storebytesF); *)
                          ("sub_ptr", cfunU sub_ptrF); ("cmp_ptr", cfunU cmp_ptrF);
                          ("non_null?", cfunU non_nullF);
                          ("malloc", cfunU mallocF); ("free", cfunU mfreeF);
                          ("memcpy", cfunU memcpyF);
                          ("capture", cfunU captureF)];
        ModSem.mn := "Mem";
        ModSem.initial_st := (match load_mem with Some m => m | None => default_mem end)↑;
      |}
  .

End MODSEM.

Local Open Scope clight_scope.

Definition Mem sk: Mod.t :=
  {|
    Mod.get_modsem := MemSem;
    Mod.sk := sk;
  |}
.
