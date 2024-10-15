Require Import CoqlibCCR.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import Any.
Require Import ModSem.
Require Import ModSemE.
Require Import ClightPlusMemRA.
Require Import ClightPlusMem1.
From compcert Require Export Ctypes Values AST Memdata Integers.

Set Implicit Arguments.

Section PROP.

  Context `{@GRA.inG Mem.t Σ}.

  (* Definition swab_func (v: val) : val := *)
  (*   match v with *)
  (*   | Vlong n => if Archi.ptr64 then Vlong n else Vundef *)
  (*   | Vint n => if negb Archi.ptr64 then Vint n else Vundef *)
  (*   | _ => Vundef *)
  (*   end. *)

End PROP.

Section SPEC.

  Context `{@GRA.inG Mem.t Σ}.

  (* uintptr_t encode(uintptr_t key, void *ptr) { *)
  (*   uintptr_t encoded; *)
  (*   encoded = (uintptr_t)ptr ^ key; *)
  (*   return encoded; *)
  (* } *)

  Definition encode_spec : fspec :=
    (mk_simple
      (fun '(key, ptr, ofs, m_ptr, tg, q) => (
        (ord_pure 10%nat),
        (fun varg => ⌜varg = [Vlong key; ptr]↑⌝
                     ** live_(m_ptr,tg,q) (Val.subl ptr (Vptrofs ofs))),
        (fun vret => ∃ iptr, ⌜vret = (Val.xorl (Vlong iptr) (Vlong key))↑⌝
                     ** live_(m_ptr,tg,q) (Val.subl ptr (Vptrofs ofs)) ** ptr (≃_ m_ptr) (Vlong iptr))
    )))%I.

  (* void *decode(uintptr_t key, uintptr_t ptr) { *)
  (*   void *decoded; *)
  (*   decoded = (void *\) (ptr ^ key); *)
  (*   return decoded; *)
  (* } *)
  
  Definition decode_spec : fspec :=
    (mk_simple
      (fun '(key, ptr) => (
        (ord_pure 10%nat),
        (fun varg => ⌜varg = [Vlong key; (Vlong ptr)]↑⌝),
        (fun vret => ⌜vret = (Val.xorl (Vlong ptr) (Vlong key))↑⌝)
    )))%I.

  (* long bar(uintptr_t key, uintptr_t ptr) { *)
  (*   long *q = decode(key, ptr); *)
  (*   return *q; *)
  (* } *)
(* { q = key ^ ptr , q |->v } {r=v. *)
  Definition bar_spec : fspec :=
    (mk_simple
      (fun '(key, ptr, qq, a, m, q, tg, ofs, qqq) => (
        (ord_pure 20%nat),
        (fun varg => ⌜varg = [Vlong key; (Vlong ptr)]↑
                  /\ ((8|Ptrofs.unsigned ofs)%Z)⌝
                          ** (qq (≃_m) Val.xorl (Vlong ptr) (Vlong key))
                          ** (qq (↦_m, q) (encode_val Mint64 (Vlong a)))
                          ** live_(m,tg,qqq) (Val.subl qq (Vptrofs ofs))),
        (fun vret => ⌜vret = (Vlong a)↑⌝ ** (qq (↦_m, q) (encode_val Mint64 (Vlong a)))
                                         ** live_(m,tg,qqq) (Val.subl qq (Vptrofs ofs)))
    )))%I.
  
  (* long foo(uintptr_t key, long *p) { *)
  (*   *p = 42; *)
  (*   uintptr_t qi = encode(key, p); *)
  (*   long ret = bar(key, qi); *)
  (*   return ret; *)
  (* } *)

  Definition foo_spec : fspec :=
    (mk_simple
      (fun '(key, ptr, m, q, tg, ofs) => (
        (ord_pure 30%nat),
        (fun varg => ∃ v, ⌜varg = [Vlong key; ptr]↑ /\ ((8|Ptrofs.unsigned ofs)%Z)⌝
                          ** (ptr (↦_m, 1) (encode_val Mint64 v))
                          ** live_(m,tg,q) (Val.subl ptr (Vptrofs ofs))
                           ),
        (fun vret => ⌜vret = (Vlong (Int64.repr 42))↑⌝)
    )))%I.

  (* sealed *)
  Definition hardeningStb : list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [
           ("encode", encode_spec);
           ("decode", decode_spec);
           ("bar", bar_spec);
           ("foo", foo_spec)
           ].
  Defined.

End SPEC.

Section SMOD.

  Context `{@GRA.inG Mem.t Σ}.

  Definition hardeningSbtb: list (gname * fspecbody) :=
    [
     ("encode", mk_pure encode_spec);
     ("decode", mk_pure decode_spec);
     ("bar", mk_pure bar_spec);
     ("foo", mk_pure foo_spec)
     ].

End SMOD.
