import set_theory.pgame
import position
import tactic
import tactic.nth_rewrite.default

universe u

/-!
# Basic deinitions about impartial (pre-)games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivilent to its negitve,
no matter what moves are played. This allows for games such as poker-nim to be classifed as
impartial.
-/

namespace pgame

local infix ` ≈ ` := pgame.equiv

/-- The definiton for a impartial game, defined using Conway induction -/
@[class] def impartial : pgame → Prop 
| G := G ≈ -G ∧ (∀ i, impartial (G.move_left i)) ∧ (∀ j, impartial (G.move_right j))
using_well_founded {dec_tac := pgame_wf_tac}

@[instance] lemma zero_impartial : impartial 0 := by tidy

@[simp] lemma impartial_def {G : pgame} : 
	G.impartial ↔ G ≈ -G ∧ (∀ i, impartial (G.move_left i)) ∧ (∀ j, impartial (G.move_right j)) := 
begin
	split,
	{	intro hi,
		unfold1 impartial at hi,
		exact hi },
	{	intro hi,
		unfold1 impartial,
		exact hi }
end

lemma impartial_neg_equiv_self (G : pgame) [h : G.impartial] : G ≈ -G :=
begin
	rw impartial_def at h,
	exact h.1
end

@[instance] lemma impartial_move_left_impartial {G : pgame} [h : G.impartial] (i : G.left_moves) : impartial (G.move_left i) :=
begin
	rw impartial_def at h,
	exact h.2.1 i,
end

@[instance] lemma impartial_move_right_impartial {G : pgame} [h : G.impartial] (j : G.right_moves) : impartial (G.move_right j) :=
begin
	rw impartial_def at h,
	exact h.2.2 j,
end

@[instance] lemma impartial_add : ∀ (G H : pgame) [hG : G.impartial] [hH : H.impartial], (G + H).impartial
| G H :=
begin
	introsI hG hH,
	rw impartial_def,
	split,
	{	apply equiv_trans _ (equiv_of_relabelling (neg_add_relabelling G H)).symm,
		apply add_congr;
		exact impartial_neg_equiv_self _	},
	split,
	{ intro i,
		equiv_rw pgame.left_moves_add G H at i,
		cases i with iG iH,
		{	rw add_move_left_inl,
			exact impartial_add (G.move_left iG) H },
		{ rw add_move_left_inr,
			exact impartial_add G (H.move_left iH) } },
	{ intro j,
		equiv_rw pgame.right_moves_add G H at j,
		cases j with jG jH,
		{ rw add_move_right_inl,
			exact impartial_add (G.move_right jG) H },
		{ rw add_move_right_inr,
			exact impartial_add G (H.move_right jH) } }
end
using_well_founded {dec_tac := pgame_wf_tac}

@[instance] lemma impartial_neg : ∀ (G : pgame) [G.impartial], (-G).impartial
| G :=
begin
	introI,
	rw impartial_def,
	split,
	{	rw neg_neg,
		symmetry,
		exact impartial_neg_equiv_self G },
	split,
	{ intro i,
		equiv_rw G.left_moves_neg at i,
		rw move_left_right_moves_neg_symm,
		exact impartial_neg (G.move_right i) },
	{ intro j,
		equiv_rw G.right_moves_neg at j,
		rw move_right_right_moves_neg_symm,
		exact impartial_neg (G.move_left j) }
end
using_well_founded {dec_tac := pgame_wf_tac}

lemma impartial_position_cases (G : pgame) [G.impartial] : G.p_position ∨ G.n_position :=
begin
  rcases G.position_cases with hl | hr | hp | hn,
  { exfalso, 
    cases hl with hpos hnonneg,
		rw ← not_lt at hnonneg,
		have hneg := lt_of_lt_of_equiv hpos G.impartial_neg_equiv_self,
		rw lt_iff_neg_gt at hneg,
		rw neg_neg at hneg,
		rw neg_zero at hneg,
		contradiction },
	{ exfalso,
		cases hr with hnonpos hneg,
		rw ← not_lt at hnonpos,
		have hpos := lt_of_equiv_of_lt G.impartial_neg_equiv_self.symm hneg,
		rw lt_iff_neg_gt at hpos,
		rw neg_neg at hpos,
		rw neg_zero at hpos,
		contradiction },
	{ left, assumption },
	{ right, assumption }
end

lemma impartial_add_self (G : pgame) [G.impartial] : (G + G).p_position :=
begin
	rw p_position_is_zero,
	apply equiv_trans,
	exact add_congr G.impartial_neg_equiv_self G.equiv_refl,
	exact add_left_neg_equiv
end

/-- A different way of viewing equivalence. I think this should work for non impartial games with cases for l- and r-positons -/
def additive_equiv (G H : pgame) [G.impartial] [H.impartial] : Prop :=
	∀ (F : pgame) [F.impartial], (G + F).p_position ↔ (H + F).p_position

lemma additive_equiv_equiv_equiv (G H : pgame) [hG : G.impartial] [hH : H.impartial] : G.additive_equiv H ↔ G ≈ H :=
begin
	split,
	{ intro heq,
		cases G.impartial_position_cases with hGp hGn,
		{ specialize heq 0, 
			rw p_position_of_equiv_iff G.add_zero_equiv at heq, 
			rw p_position_of_equiv_iff H.add_zero_equiv at heq, 
			rw p_position_is_zero at hGp heq,
			rw p_position_is_zero at heq,
			have hHp := heq.1 hGp,
			apply equiv_trans,
			exact hGp,
			exact hHp.symm },
		{ split,
			{ rw le_iff_sub_nonneg,
				specialize heq (-G),
				rw p_position_of_equiv_iff add_comm_equiv at heq,
				rw p_position_of_equiv_iff add_left_neg_equiv at heq, 
				have hHGp := heq.1 zero_p_postition,
				exact hHGp.2 },
			{ rw le_iff_sub_nonneg,
				specialize heq (-H),
				nth_rewrite 1 p_position_of_equiv_iff add_comm_equiv at heq,
				rw p_position_of_equiv_iff add_left_neg_equiv at heq,
				have hGHp := heq.2 zero_p_postition,
				exact hGHp.2 } } },
	{ intro heq,
		intros F hf,
		rw p_position_is_zero,
		rw p_position_is_zero,
		split,
		{ intro hGF,
			apply equiv_trans,
			apply add_congr,
			exact heq.symm,
			refl,
			exact hGF },
		{ intro hHF,
			apply equiv_trans,
			apply add_congr,
			exact heq,
			refl,
			exact hHF } }
end

lemma equiv_iff_sum_p_position (G H : pgame) [G.impartial] [H.impartial] : G ≈ H ↔ (G + H).p_position :=
begin
	split,
	{ intro heq,
		apply p_position_of_equiv,
		apply add_congr,
		refl,
		exact heq,
		exact G.impartial_add_self },
	{ intro hGHp,
		split,
		{ rw le_iff_sub_nonneg,
			apply le_trans,
			use hGHp.2,
			apply le_trans,
			use add_comm_le,
			apply le_of_le_of_equiv,
			refl,
			apply add_congr,
			refl,
			exact G.impartial_neg_equiv_self },
		{ rw le_iff_sub_nonneg,
			apply le_trans,
			use hGHp.2,
			apply le_of_le_of_equiv,
			refl,
			apply add_congr,
			refl,
			exact H.impartial_neg_equiv_self } }
end

lemma impartial_p_position_symm (G : pgame) [G.impartial] : G.p_position ↔ G ≤ 0 :=
begin
	split,
	{ intro hp,
		exact hp.1 },
	{ intro hneg,
		use hneg,
		rw zero_le_iff_neg_le_zero,
		apply le_of_equiv_of_le,
		exact (impartial_neg_equiv_self G).symm,
		assumption }
end

lemma impartial_n_position_symm (G : pgame) [G.impartial] : G.n_position ↔ G < 0 :=
begin
	split,
	{ intro hn,
		exact hn.2 },
	{ intro hneg,
		split,
		rw lt_iff_neg_gt,
		rw neg_zero,
		apply lt_of_equiv_of_lt,
		exact (impartial_neg_equiv_self G).symm,
		exact hneg,
		exact hneg }
end

lemma impartial_p_position_symm' (G : pgame) [G.impartial] : G.p_position ↔ 0 ≤ G :=
begin
	split,
	{ intro hp,
		exact hp.2 },
	{ intro hpos,
		split,
		rw le_zero_iff_zero_le_neg,
		apply le_of_le_of_equiv,
		exact hpos,
		exact (impartial_neg_equiv_self G),
		assumption }
end

lemma impartial_n_position_symm' (G : pgame) [G.impartial] : G.n_position ↔ 0 < G :=
begin
	split,
	{ intro hn,
		exact hn.1 },
	{ intro hpos,
		use hpos,
		rw lt_iff_neg_gt,
		rw neg_zero,
		apply lt_of_lt_of_equiv,
		exact hpos,
		exact (impartial_neg_equiv_self G) }
end

lemma no_good_left_moves_iff_p_position (G : pgame) [G.impartial] : (∀ (i : G.left_moves), (G.move_left i).n_position) ↔ G.p_position :=
begin
	split,
	{	intro hbad,
		rw impartial_p_position_symm,
		rw le_def_lt,
		split,
		{ intro i,
			specialize hbad i,
			exact hbad.2 },
		{ intro j,
			exact pempty.elim j } },
	{ intro hp,
		intro i,
		rw impartial_n_position_symm,
		rw impartial_p_position_symm at hp,
		rw le_def_lt at hp,
		cases hp with hp,
		specialize hp i,
		assumption }
end

lemma no_good_right_moves_iff_p_position (G : pgame) [G.impartial] : (∀ (j : G.right_moves), (G.move_right j).n_position) ↔ G.p_position :=
begin
	split,
	{ intro hbad,
		rw impartial_p_position_symm',
		rw le_def_lt,
		split,
		{ intro i,
			exact pempty.elim i },
		{ intro j,
			specialize hbad j,
			exact hbad.1 } },
	{ intro hp,
		intro j,
		rw impartial_n_position_symm',
		rw impartial_p_position_symm' at hp,
		rw le_def_lt at hp,
		cases hp with _ hp,
		specialize hp j,
		assumption }
end

lemma good_left_move_iff_n_position (G : pgame) [G.impartial] : (∃ (i : G.left_moves), (G.move_left i).p_position) ↔ G.n_position :=
begin
	split,
	{ rintro ⟨ i, hi ⟩,
		rw impartial_n_position_symm',
		rw lt_def_le,
		left,
		use i,
		exact hi.2 },
	{ intro hn,
		rw impartial_n_position_symm' at hn,
		rw lt_def_le at hn,
		cases hn with hn hn,
		{ cases hn with i hi,
			use i,
			rw impartial_p_position_symm',
			exact hi },
		{ cases hn with j,
			exact pempty.elim j } }
end

lemma good_right_move_iff_n_position (G : pgame) [G.impartial] : (∃ j : G.right_moves,  (G.move_right j).p_position) ↔ G.n_position :=
begin
	split,
	{ rintro ⟨ j, hj ⟩,
		rw impartial_n_position_symm,
		rw lt_def_le,
		right,
		use j,
		exact hj.1 },
	{ intro hn,
		rw impartial_n_position_symm at hn,
		rw lt_def_le at hn,
		cases hn with hn hn,
		{ cases hn with i,
			exact pempty.elim i },
		{ cases hn with j hj,
			use j,
			rw impartial_p_position_symm,
			exact hj } }
end

end pgame
