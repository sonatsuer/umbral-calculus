/-
# Conservativity, for the umbral language

`Core/Conservativity.lean` shows that the Kripke denotation of an embedded
term of the restricted language simulates its denotation there, for an arbitrary allocation
structure. This file reads that theorem at the moment worlds of
`Umbral/Worlds.lean` (write-up, Chapter 3, conservativity).

**The statement.** Let `t` be a scalar-valued expression of the restricted
language in `m` umbrae, `w` a world, and `u` an `m`-tuple of its names. Read `t` as a term of
the full language, evaluate it at `w`, and apply it to the thirteen methods of the moment
dictionary and to `u`, each at the identity of `w`. The result is the value
the restricted language gives `t` at the moment dictionary of `w`'s moments and at `u`.

So every theorem about `Restricted.denN` is a theorem about denotations in the
full language. An expression of the restricted language does not receive `mk`, so
it cannot allocate. That is the sense in which the restricted language is the
allocation-free fragment of the full language.
-/

import FreeThms.Core.Conservativity
import FreeThms.Umbral.Worlds

namespace FreeThms.Umbral.Full

open MvPolynomial (X C rename)
open FreeThms.Umbral.Restricted (Slot)
open FreeThms.Kripke (QTy QSim SimEnv evalC)

noncomputable section

variable {k : Type} [CommRing k]

/-- The simulation environment at `w` that instantiates `K`, `U` and `A` at the
three sorts. Its relations are equality. -/
abbrev simEnv (w : World k) : SimEnv (base k) w 3 :=
  SimEnv.cons (base k) w (SimEnv.cons (base k) w (SimEnv.cons (base k) w (SimEnv.nil (base k) w)
    (.base .K)) (.base .U)) (.base .A)

/-- Apply the reading in the full language of a curried function of `m` umbrae to a tuple, at
the identity each time. -/
def applyEmbedded (w : World k) : (m : ℕ) → Val (QTy.embed (Restricted.umbraArrows m)) w →
    (Fin m → Fin w.size) → k
  | 0, c, _ => c
  | m + 1, f, u => applyEmbedded w m (f w (Hom.id w) (u 0)) (fun i => u i.succ)

/-- **The reading of an expression of the restricted language in the full
language** at the moment dictionary of a world and a tuple of its names. -/
def denEmbedded (m : ℕ) (t : PClosedTm (Restricted.manyUmbraTy m)) (w : World k)
    (u : Fin m → Fin w.size) : k :=
  applyEmbedded w m (applyMethods w
    (evalC (base k) (Kripke.QTm.embed t) w (.base .K) (.base .U) (.base .A))) u

/-- The thirteen methods of the moment dictionary of the full language simulate those
of the moment dictionary of the restricted language. -/
theorem applyMethods_sim (w : World k) {body : PTy 3}
    {f : Val (QTy.embed (Restricted.dictTy body)) w}
    {g : PTyD (Kripke.atWorld (base k) w) (Restricted.dictTy body) (simEnv w).r}
    (h : QSim (base k) w (Restricted.dictTy body) (simEnv w) f g) :
    QSim (base k) w body (simEnv w) (applyMethods w f)
      (g (Restricted.momDict w.mom).zeroK (Restricted.momDict w.mom).oneK
        (Restricted.momDict w.mom).addK (Restricted.momDict w.mom).mulK
        (Restricted.momDict w.mom).negK (Restricted.momDict w.mom).zeroA
        (Restricted.momDict w.mom).oneA (Restricted.momDict w.mom).addA
        (Restricted.momDict w.mom).mulA (Restricted.momDict w.mom).negA
        (Restricted.momDict w.mom).constA (Restricted.momDict w.mom).injA
        (Restricted.momDict w.mom).evalA) := by
  refine h _ _ rfl _ _ rfl _ _ ?addK _ _ ?mulK _ _ ?negK _ _ rfl _ _ rfl _ _ ?addA _ _ ?mulA
    _ _ ?negA _ _ ?constA _ _ ?injA _ _ ?evalA
  case addK => rintro (x : k) _ rfl (y : k) _ rfl; rfl
  case mulK => rintro (x : k) _ rfl (y : k) _ rfl; rfl
  case negK => rintro (x : k) _ rfl; rfl
  case addA =>
    rintro (p : MvPolynomial (Fin w.size) k) _ rfl (q : MvPolynomial (Fin w.size) k) _ rfl
    show rename _root_.id p + q = p + q
    rw [MvPolynomial.rename_id_apply]
  case mulA =>
    rintro (p : MvPolynomial (Fin w.size) k) _ rfl (q : MvPolynomial (Fin w.size) k) _ rfl
    show rename _root_.id p * q = p * q
    rw [MvPolynomial.rename_id_apply]
  case negA => rintro (p : MvPolynomial (Fin w.size) k) _ rfl; rfl
  case constA => rintro (c : k) _ rfl; rfl
  case injA => rintro (x : Fin w.size) _ rfl; rfl
  case evalA => rintro (p : MvPolynomial (Fin w.size) k) _ rfl; rfl

/-- Simulated curried functions of `m` umbrae agree on every tuple. -/
theorem applyEmbedded_sim (w : World k) : (m : ℕ) →
    {f : Val (QTy.embed (Restricted.umbraArrows m)) w} →
    {g : PTyD (Kripke.atWorld (base k) w) (Restricted.umbraArrows m) (simEnv w).r} →
    QSim (base k) w (Restricted.umbraArrows m) (simEnv w) f g → (u : Fin m → Fin w.size) →
    applyEmbedded w m f u = Restricted.applyN (simEnv w).r m g u
  | 0, _, _, h, _ => h
  | m + 1, _, _, h, u => applyEmbedded_sim w m (h (u 0) (u 0) rfl) (fun i => u i.succ)

/--
**Conservativity of the full language over the restricted language, for the
umbral language.** The reading of an expression of the restricted language in the
full language, at the moment dictionary of a world, is its denotation in the
restricted language at the moment dictionary of that world's moments.

The proof is `Kripke.conservative_closed` at the moment worlds, read at the
three sorts and at the moment dictionary.
-/
theorem conservative (m : ℕ) (t : PClosedTm (Restricted.manyUmbraTy m)) (w : World k)
    (u : Fin m → Fin w.size) :
    denEmbedded m t w u =
      Restricted.denN m k (Fin w.size) (MvPolynomial (Fin w.size) k) (Restricted.momDict w.mom) t u :=
  applyEmbedded_sim w m
    (applyMethods_sim w (Kripke.conservative_closed (base k) w t (.base .K) (.base .U)
      (.base .A))) u

end

end FreeThms.Umbral.Full
