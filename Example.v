Require Import Fsub_Definitions.
Require Import Fsub_Infrastructure.

Check (exp_abs (typ_capt cset_universal typ_top) 0).
Check (typ_arrow (typ_capt cset_universal typ_top)
                  (typ_capt (cset_set {} (NatSet.F.singleton 0)) typ_top)).

Lemma ezy_pzy_lemon_sqzy :
   typing empty
          (exp_abs (typ_capt cset_universal typ_top) 0)
          (typ_capt {}C
                    (typ_arrow (typ_capt cset_universal typ_top)
                               (typ_capt (cset_set {}
                                (NatSet.F.singleton 0)) typ_top)))
.
Proof with eauto.
   pick fresh x and apply typing_abs.
   - simpl.
     Hint Unfold open_ee : core.
     Hint Unfold open_ct : core.
     Hint Unfold open_cset : core.
     repeat (unfold open_tt, open_tpt, open_te, open_ee, open_ct,
open_cpt, open_cset; simpl).
     Check (NatSet.F.mem 0 (NatSet.F.singleton 0)).
     replace (NatSet.F.mem 0 (NatSet.F.singleton 0)) with true.
     2 : admit.
     replace (cset_set (singleton x `union` {})
                       (NatSet.F.union {}N (NatSet.F.remove 0
(NatSet.F.singleton 0))))
       with (x : captureset).
     apply typing_var with (C := cset_universal).
     + econstructor...
     + unfold binds.
       simpl.
       assert (x = x) as COME_ON by trivial.
       assert ((x == x) = (inl COME_ON : {x = x} + {x <> x})).
       replace  with .
       Check (x == x).
       Locate "_ == _".S
       Locate "_ + _".
       sum
       eq_atom_dec
       atoms
       replace (x == x) with {x = x}.
