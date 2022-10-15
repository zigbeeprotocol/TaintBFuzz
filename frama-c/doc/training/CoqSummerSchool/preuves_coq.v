Lemma div_def : 
  (forall (i_27:Z), i_27 = (2 * ((Zdiv i_27 2))) \/ i_27 =
   (2 * ((Zdiv i_27 2)) + 1)).
Proof.
cut (2>0).
intros H i_27;
generalize (Z_div_mod_eq i_27 2 H).
generalize (Z_mod_lt i_27 2 H).
omega.
eauto with zarith.

Save.

Lemma div_le : 
  (forall (i_28:Z),
   (0 <= i_28 -> 0 <= ((Zdiv i_28 2)) /\ ((Zdiv i_28 2)) <= i_28)).
Proof.
intros i_28;
cut (2>0).
intros H;
generalize (Z_div_mod_eq i_28 2 H).
generalize (Z_mod_lt i_28 2 H).
omega.
eauto with zarith.

 Lemma div_mod : 
  (forall (i_28:Z),
   (forall (j_3:Z), (i_28 + 2 * j_3 - 2 * ((Zdiv (i_28 + 2 * j_3) 2))) =
    (i_28 - 2 * ((Zdiv i_28 2))))).
									
intros i j.
cut (2>0).
intros H;
generalize (Z_mod_plus i j 2 H).
generalize (Z_div_mod_eq i 2 H).
generalize (Z_div_mod_eq (i+2*j) 2 H).
intros H1 H2 H3.
cut (i + 2 * j - 2 * ((i + 2 * j) / 2) = (i+2*j) mod 2).
intros H4; rewrite H4.
cut (i - 2 * (i / 2) = i mod 2).
intros H5; rewrite H5; auto.
cut (2*j = j*2).
intros H6. rewrite H6; tauto.
auto with zarith.
auto with zarith.
auto with zarith.
auto with zarith.

  
post-cond1
Proof.
intuition.
rewrite HW_11; 
rewrite HW_10; 
rewrite HW_9; 
rewrite HW_8; 
rewrite HW_7; 
rewrite HW_6; 
rewrite HW_5.
cut (2>0); eauto with zarith.
intros Hgt.
generalize (integer_of_int32 (select int_P_int_M_p_20 p)).
generalize (integer_of_int32 (select int_P_int_M_q_21 q)).
intros x y.
generalize (Z_div_mod_eq (y+x) 2 Hgt); intros Heucl1.
generalize (Z_div_mod_eq (y-x) 2 Hgt); intros Hrem1.
generalize (Z_mod_lt (y+x) 2 Hgt); intros Heucl2.
generalize (Z_mod_lt (y-x) 2 Hgt); intros Hrem2.
eapply (Zmult_reg_l ((y-x)/2 + x) ((y+x)/2) 2).
auto with zarith.
omega. 
Save.

post condition 2
intuition.
(* FILL PROOF HERE *)
rewrite HW_19; 
rewrite HW_18; 
rewrite HW_17; 
rewrite HW_16; 
rewrite HW_15; 
rewrite HW_14; 
rewrite HW_13.
cut (2>0); eauto with zarith.
intros Hgt.
generalize (integer_of_int32 (select int_P_int_M_p_20 p)).
generalize (integer_of_int32 (select int_P_int_M_q_21 q)).
intros x y.
generalize (Z_div_mod_eq (y+x) 2 Hgt); intros Heucl1.
generalize (Z_div_mod_eq (x-y) 2 Hgt); intros Hrem1.
generalize (Z_mod_lt (y+x) 2 Hgt); intros Heucl2.
generalize (Z_mod_lt (x-y) 2 Hgt); intros Hrem2.
eapply (Zmult_reg_l ((x-y)/2 + y) ((y+x)/2) 2).
auto with zarith.
omega. 
