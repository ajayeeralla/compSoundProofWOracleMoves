Load "Pi4.v".



(**************************************************************************************************)



Theorem DDH_two_RRS1 : phi11 ~ phi31.

Proof.  try (unfold phi11, phi21, phi10, phi20, t10, t20, t11,t12, t21,t22). unfold qa0000, qb0000, mphi10, mphi20, phi10. try (unfold phi11, phi21, phi10, phi20, t10, t20, t11,t12, t21,t22). simpl.  try unfold grn21, grn21, msgt10, msgt11, msgt20, msgt21. simpl. reflexivity. Qed.

Theorem DDH_two_RRS2 : phi12 ~ phi22.
Proof. repeat (try (unfold phi12, phi22 ,phi11, phi21, phi10, phi20, t10, t20, t11,t12, t21,t22, t13, t23)). simpl. unfold qa0000, qb0000, qa1000, qa0010, qa0001, qa0100,qb1000, qb0010, qb0001, qb0100, mphi10, mphi20, phi10. simpl. try (unfold phi11, phi21, phi10, phi20, t10, t20, t11,t12, t21,t22, t13). simpl.  try unfold  grn2, grn22, grn21, grn21, msgt10, msgt11, msgt20, msgt21, mphi21, mphi11. simpl. reflexivity. Qed.

Theorem DDH_two_RRS3: phi13~ phi23.
Proof.  reflexivity. Qed.

Theorem DDH_two_RRS4: (Fresh [0; 1;2; 3] [] = true) -> phi14 ~ phi24.
Proof .  intros; pose proof (DDH); apply DDH in H;  repeat try unfold phi15, phi25, phi14, phi24, phi13, phi23, phi12, phi22 ,phi11, phi21, phi10, phi20 . repeat try unfold t10, t20, t11,t12, t21,t22, t13, t23, t14, t24, t15, t25, t16, t26.  try unfold mphi15 , mphi14 , mphi13 , mphi12. try unfold mphi11, mphi10. try simpl.  try unfold mphi25,mphi24,  mphi23,mphi22 . try unfold mphi21,  mphi20. simpl.
repeat try unfold msgt10, msgt20, msgt11, msgt12, msgt21, msgt22, msgt13, msgt23, msgt14, msgt24, msgt15, msgt25, msgt16, msgt26;
 repeat try unfold grn21, grn2, grn3, grn4, grn21, grn22, grn23, grn24; repeat try unfold mf1ph10rn1,  mf2ph110rn1,   mf2ph11rn1,  mf2ph11rn2,  mf3ph12rn1, mf3ph12rn2,  mf1ph20rn1,  mf2ph20rn1,   mf2ps1rn1,  mf2ps1rn2,  mf3ps2rn1, mf3ps2rn2; repeat try simpl;
repeat try unfold q0000, q1000 , q0010,q0100,q0001 ,q2000,q1100 ,q1001 ,q0110,q0200,q1000_s,q0010_s,q0100_s,q0001_s,q2100,q1200,q2001,q0210,
 q0120,q2000_s, q1100_s, q1001_s, q0110_s,q0200_s,q1000_ss,q0010_ss, q0100_ss,q0001_ss,q2200,q2100_s,q1200_s,q2001_s,q0210_s,q0120_s,q2000_ss,q1100_ss ,q1001_ss,q0110_ss,q0200_ss,
 q1000_sss,q0010_sss,q0100_sss,q0001_sss;
repeat try unfold qb0000, qb1000 , qb0010,qb0100,qb0001 ,qb2000,qb1100 ,qb1001 ,qb0110,qb0200,qb1000_s,qb0010_s,qb0100_s,qb0001_s,qb2100,qb1200,qb2001,qb0210,
 qb0120,qb2000_s, qb1100_s, qb1001_s, qb0110_s,qb0200_s,qb1000_ss,qb0010_ss, qb0100_ss,qb0001_ss,qb2200,qb2100_s,qb1200_s,qb2001_s,qb0210_s,qb0120_s,qb2000_ss,qb1100_ss ,qb1001_ss,qb0110_ss,qb0200_ss,
 qb1000_sss,qb0010_sss,qb0100_sss,qb0001_sss.

 repeat try unfold phi15, phi25, phi14, phi24, phi13, phi23, phi12, phi22 ,phi11, phi21, phi10, phi20 ;  repeat try unfold t10, t20, t11,t12, t21,t22, t13, t23, t14, t24, t15, t25, t16, t26. repeat try unfold mphi15, mphi25, mphi14, mphi24, mphi13, mphi23, mphi12, mphi22 ,mphi11, mphi21, mphi10, mphi20. 
 try unfold mphi15 , mphi14 , mphi13 , mphi12. try unfold mphi11, mphi10. try simpl.  try unfold mphi25,mphi24,  mphi23,mphi22 . try unfold mphi21,  mphi20. simpl.
repeat try unfold msgt10, msgt20, msgt11, msgt12, msgt21, msgt22, msgt13, msgt23, msgt14, msgt24, msgt15, msgt25, msgt16, msgt26;
 repeat try unfold grn1, grn2, grn3, grn4, grn21, grn22, grn23, grn24; repeat try unfold mf1ph10rn1,  mf2ph10rn1,   mf2ph11rn1,  mf2ph11rn2,  mf3ph12rn1, mf3ph12rn2, mf3ph11rn2,  mf1ph20rn1,  mf2ph20rn1,   mf2ps1rn1,  mf2ps1rn2,  mf3ps2rn1, mf3ps2rn2, mf3ps1rn2; repeat try simpl;
repeat try unfold q0000, q1000 , q0010,q0100,q0001 ,q2000,q1100 ,q1001 ,q0110,q0200,q1000_s,q0010_s,q0100_s,q0001_s,q2100,q1200,q2001,q0210,
 q0120,q2000_s, q1100_s, q1001_s, q0110_s,q0200_s,q1000_ss,q0010_ss, q0100_ss,q0001_ss,q2200,q2100_s,q1200_s,q2001_s,q0210_s,q0120_s,q2000_ss,q1100_ss ,q1001_ss,q0110_ss,q0200_ss,
 q1000_sss,q0010_sss,q0100_sss,q0001_sss;
repeat try unfold qb0000, qb1000 , qb0010,qb0100,qb0001 ,qb2000,qb1100 ,qb1001 ,qb0110,qb0200,qb1000_s,qb0010_s,qb0100_s,qb0001_s,qb2100,qb1200,qb2001,qb0210,
 qb0120,qb2000_s, qb1100_s, qb1001_s, qb0110_s,qb0200_s,qb1000_ss,qb0010_ss, qb0100_ss,qb0001_ss,qb2200,qb2100_s,qb1200_s,qb2001_s,qb0210_s,qb0120_s,qb2000_ss,qb1100_ss ,qb1001_ss,qb0110_ss,qb0200_ss,
 qb1000_sss,qb0010_sss,qb0100_sss,qb0001_sss.
 
 try unfold mphi15 , mphi14 , mphi13 , mphi12. try unfold mphi11, mphi10. try simpl.  try unfold mphi25,mphi24,  mphi23,mphi22 . try unfold mphi21,  mphi20. simpl.

Admitted.

Theorem DDH_two_RRS5: [t15] ~ [t25].

Proof.    repeat try unfold phi15, phi25, phi14, phi24, phi13, phi23, phi12, phi22 ,phi11, phi21, phi10, phi20 . repeat try unfold t10, t20, t11,t12, t21,t22, t13, t23, t14, t24, t15, t25, t16, t26.  try unfold mphi15 , mphi14 , mphi13 , mphi12. try unfold mphi11, mphi10. try simpl.  try unfold mphi25,mphi24,  mphi23,mphi22 . try unfold mphi21,  mphi20. simpl.
repeat try unfold msgt10, msgt20, msgt11, msgt12, msgt21, msgt22, msgt13, msgt23, msgt14, msgt24, msgt15, msgt25, msgt16, msgt26;
 repeat try unfold grn1, grn2, grn3, grn4, grn21, grn22, grn23, grn24; repeat try unfold mf1ph10rn1,  mf2ph10rn1,   mf2ph11rn1,  mf2ph11rn2,  mf3ph12rn1, mf3ph12rn2,  mf1ph20rn1,  mf2ph20rn1,   mf2ps1rn1,  mf2ps1rn2,  mf3ps2rn1, mf3ps2rn2; repeat try simpl;
repeat try unfold q0000, q1000 , q0010,q0100,q0001 ,q2000,q1100 ,q1001 ,q0110,q0200,q1000_s,q0010_s,q0100_s,q0001_s,q2100,q1200,q2001,q0210,
 q0120,q2000_s, q1100_s, q1001_s, q0110_s,q0200_s,q1000_ss,q0010_ss, q0100_ss,q0001_ss,q2200,q2100_s,q1200_s,q2001_s,q0210_s,q0120_s,q2000_ss,q1100_ss ,q1001_ss,q0110_ss,q0200_ss,
 q1000_sss,q0010_sss,q0100_sss,q0001_sss;
repeat try unfold qb0000, qb1000 , qb0010,qb0100,qb0001 ,qb2000,qb1100 ,qb1001 ,qb0110,qb0200,qb1000_s,qb0010_s,qb0100_s,qb0001_s,qb2100,qb1200,qb2001,qb0210,
 qb0120,qb2000_s, qb1100_s, qb1001_s, qb0110_s,qb0200_s,qb1000_ss,qb0010_ss, qb0100_ss,qb0001_ss,qb2200,qb2100_s,qb1200_s,qb2001_s,qb0210_s,qb0120_s,qb2000_ss,qb1100_ss ,qb1001_ss,qb0110_ss,qb0200_ss,
 qb1000_sss,qb0010_sss,qb0100_sss,qb0001_sss.


repeat try unfold phi15, phi25, phi14, phi24, phi13, phi23, phi12, phi22 ,phi11, phi21, phi10, phi20 ;  repeat try unfold t10, t20, t11,t12, t21,t22, t13, t23, t14, t24, t15, t25, t16, t26. repeat try unfold mphi15, mphi25, mphi14, mphi24, mphi13, mphi23, mphi12, mphi22 ,mphi11, mphi21, mphi10, mphi20. 
 try unfold mphi15 , mphi14 , mphi13 , mphi12. try unfold mphi11, mphi10. try simpl.  try unfold mphi25,mphi24,  mphi23,mphi22 . try unfold mphi21,  mphi20. simpl.
repeat try unfold msgt10, msgt20, msgt11, msgt12, msgt21, msgt22, msgt13, msgt23, msgt14, msgt24, msgt15, msgt25, msgt16, msgt26;
 repeat try unfold grn1, grn2, grn3, grn4, grn21, grn22, grn23, grn24; repeat try unfold mf1ph10rn1,  mf2ph10rn1,   mf2ph11rn1,  mf2ph11rn2,  mf3ph12rn1, mf3ph12rn2, mf3ph11rn2,  mf1ph20rn1,  mf2ph20rn1,   mf2ps1rn1,  mf2ps1rn2,  mf3ps2rn1, mf3ps2rn2, mf3ps1rn2; repeat try simpl;
repeat try unfold q0000, q1000 , q0010,q0100,q0001 ,q2000,q1100 ,q1001 ,q0110,q0200,q1000_s,q0010_s,q0100_s,q0001_s,q2100,q1200,q2001,q0210,
 q0120,q2000_s, q1100_s, q1001_s, q0110_s,q0200_s,q1000_ss,q0010_ss, q0100_ss,q0001_ss,q2200,q2100_s,q1200_s,q2001_s,q0210_s,q0120_s,q2000_ss,q1100_ss ,q1001_ss,q0110_ss,q0200_ss,
 q1000_sss,q0010_sss,q0100_sss,q0001_sss;
repeat try unfold qb0000, qb1000 , qb0010,qb0100,qb0001 ,qb2000,qb1100 ,qb1001 ,qb0110,qb0200,qb1000_s,qb0010_s,qb0100_s,qb0001_s,qb2100,qb1200,qb2001,qb0210,
 qb0120,qb2000_s, qb1100_s, qb1001_s, qb0110_s,qb0200_s,qb1000_ss,qb0010_ss, qb0100_ss,qb0001_ss,qb2200,qb2100_s,qb1200_s,qb2001_s,qb0210_s,qb0120_s,qb2000_ss,qb1100_ss ,qb1001_ss,qb0110_ss,qb0200_ss,
 qb1000_sss,qb0010_sss,qb0100_sss,qb0001_sss.

repeat try unfold phi15, phi25, phi14, phi24, phi13, phi23, phi12, phi22 ,phi11, phi21, phi10, phi20 ;  repeat try unfold t10, t20, t11,t12, t21,t22, t13, t23, t14, t24, t15, t25, t16, t26. repeat try unfold mphi15, mphi25, mphi14, mphi24, mphi13, mphi23, mphi12, mphi22 ,mphi11, mphi21, mphi10, mphi20. 
 try unfold mphi15 , mphi14 , mphi13 , mphi12. try unfold mphi11, mphi10. try simpl.  try unfold mphi25,mphi24,  mphi23,mphi22 . try unfold mphi21,  mphi20. simpl.
repeat try unfold msgt10, msgt20, msgt11, msgt12, msgt21, msgt22, msgt13, msgt23, msgt14, msgt24, msgt15, msgt25, msgt16, msgt26;
 repeat try unfold grn1, grn2, grn3, grn4, grn21, grn22, grn23, grn24; repeat try unfold mf1ph10rn1,  mf2ph10rn1,   mf2ph11rn1,  mf2ph11rn2,  mf3ph12rn1, mf3ph12rn2, mf3ph11rn2,  mf1ph20rn1,  mf2ph20rn1,   mf2ph21rn1,  mf2ph21rn2,  mf3ps2rn1, mf3ps2rn2, mf3ph21rn2; repeat try simpl;
repeat try unfold q0000, q1000 , q0010,q0100,q0001 ,q2000,q1100 ,q1001 ,q0110,q0200,q1000_s,q0010_s,q0100_s,q0001_s,q2100,q1200,q2001,q0210,
 q0120,q2000_s, q1100_s, q1001_s, q0110_s,q0200_s,q1000_ss,q0010_ss, q0100_ss,q0001_ss,q2200,q2100_s,q1200_s,q2001_s,q0210_s,q0120_s,q2000_ss,q1100_ss ,q1001_ss,q0110_ss,q0200_ss,
 q1000_sss,q0010_sss,q0100_sss,q0001_sss;
repeat try unfold qb0000, qb1000 , qb0010,qb0100,qb0001 ,qb2000,qb1100 ,qb1001 ,qb0110,qb0200,qb1000_s,qb0010_s,qb0100_s,qb0001_s,qb2100,qb1200,qb2001,qb0210,
 qb0120,qb2000_s, qb1100_s, qb1001_s, qb0110_s,qb0200_s,qb1000_ss,qb0010_ss, qb0100_ss,qb0001_ss,qb2200,qb2100_s,qb1200_s,qb2001_s,qb0210_s,qb0120_s,qb2000_ss,qb1100_ss ,qb1001_ss,qb0110_ss,qb0200_ss,
 qb1000_sss,qb0010_sss,qb0100_sss,qb0001_sss. 

Admitted.


