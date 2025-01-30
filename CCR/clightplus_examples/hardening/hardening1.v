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


  (* long bar(long k, uintptr_t ep, long x) { *)
  (*   long *q = decode(k, ep); *)
  (*   *q = x; *)
  (*   return *q;                    *)
  (* } *)

  (* PRE { p ~^m ip * p |->^m _ * ep = xor ip k } *)
  (* POST { r. r = x * p |->^m x } *)


  Definition bar_spec : fspec :=
    (mk_simple
      (fun '(p, ip, m, ofs, ep, x, key) => (
        (ord_pure 30%nat),
        (fun varg => ∃ dv, ⌜varg = [Vlong key; Vlong ep; Vlong x]↑
                        /\ ((8|Ptrofs.unsigned ofs)%Z)
                        (* /\ (strings.length dv = size_chunk_nat Mint64) *)
                        /\ (Vlong ep = Val.xorl (Vlong ip) (Vlong key))⌝
                          ** (p (≃_ m) (Vlong ip))
                          ** (p (↦_m, 1) (encode_val Mint64 dv))
                          ** p ⊨ m # ofs
                           ),
        (fun vret => ⌜vret = (Vlong x)↑⌝
                          ** (p (↦_m, 1) (encode_val Mint64 (Vlong x)))
        )
    )))%I.
  
  (* Definition bar_spec : fspec := *)
  (*   (mk_simple *)
  (*     (fun '(p, ip, m, ofs, ep, x, key, dv) => ( *)
  (*       (ord_pure 20%nat), *)
  (*       (fun varg => ⌜varg = [Vlong key; Vlong ep; Vlong x]↑ *)
  (*                 /\ ((8|Ptrofs.unsigned ofs)%Z) *)
  (*                 /\ (Vlong ep = Val.xorl (Vlong ip) (Vlong key))⌝ *)
  (*                     ** (p (≃_ m) (Vlong ip)) *)
  (*                     ** (p (↦_m, 1) (encode_val Mint64 dv)) *)
  (*                     ** p ⊨ m # ofs *)
  (*       (* ** live_(m,tg,qqq) (Val.subl qq (Vptrofs ofs)) *) *)
  (*       ), *)
  (*       (fun vret => ⌜vret = (Vlong x)↑⌝ ** (p (↦_m, 1) (encode_val Mint64 (Vlong x))) *)
  (*                           (* ** live_(m,tg,qqq) (Val.subl qq (Vptrofs ofs)) *) *)

  (*       ) *)
  (*   )))%I. *)


  (* // Function that creates encoded pointer *)
  (* long foo(long *p, long k, long x) { *)
  (*     uintptr_t ep = encode(k, p);  // pointer encoding *)
  (*     bar(k, ep, x);     // pass encoded pointer *)
  (*     return *p;  // *p = x *)
  (* } *)

  (* PRE { p |->^m _ * live^m (p - 0) } *)
  (* POST { r. r = x * p |->^m x * live^m (p - 0) } *)
  Definition foo_spec : fspec :=
    (mk_simple
      (fun '(p, m, q, tg, ofs, x, key) => (
        (ord_pure 70%nat),
        (fun varg => ∃ dv, ⌜varg = [p; Vlong key; Vlong x]↑
                        /\ ((8|Ptrofs.unsigned ofs)%Z)⌝
                        (* /\ (strings.length dv = size_chunk_nat Mint64) *)
                          ** (p (↦_m, 1) (encode_val Mint64 dv))
                          ** live_(m,tg,q) (Val.subl p (Vptrofs ofs))
                           ),
        (fun vret => ⌜vret = (Vlong x)↑⌝
                          ** (p (↦_m, 1) (encode_val Mint64 (Vlong x)))
                          ** live_(m,tg,q) (Val.subl p (Vptrofs ofs)))
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
