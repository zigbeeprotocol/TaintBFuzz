intros i i_pos.
split.
apply Z_div_pos; auto with zarith.
elim (Zle_lt_or_eq _ _ i_pos).
intro i_spos; apply (Zlt_le_weak (i/2) i).
apply Z_div_lt; auto with zarith.
intros Heq; rewrite <- Heq; compute.
intros Habs; discriminate Habs.
