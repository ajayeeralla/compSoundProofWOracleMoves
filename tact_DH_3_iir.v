Load "DH_3_iir" .
(***********unfold****************)

Ltac unf_phi := try unfold phi0, phi1, phi2, phi3, phi4, phi24 ; try unfold   phi34, phi41, phi42, phi43, phi44.
Ltac unf_trm:=  try unfold  t12, t13,t14, t15,t25, t35, t45.

Ltac unf_qa := try unfold  qa000, qa010, qa001; try unfold qa010_s, qa100_s, qa001_s; try unfold qa010_ss, qa100_ss, qa001_ss; try unfold qa200, qa110, qa020, qa101, qa002, qa011; try unfold qa200, qa110_s, qa020_s, qa101_s, qa002_s, qa011_s;  try unfold  qa210,  qa120, qa111, qa012, qa102, qa201, qa021, qa300, qa030. 
 
Ltac unf_qb :=  try unfold  qb201, qb021, qb101_s, qb200_s, qb020_s, qb100_ss, qb100_ss,  qb121, qb111_s, qb120_s, qb021_s, qb110_ss, qb101_ss, qb011_ss, qb100_sss, qb010_sss.

Ltac unf_qc :=  try unfold  qc201, qc021, qc101_s, qc101_s, qc020_s, qc100_ss, qc100_ss,  qc121, qc111_s, qc120_s, qc210_s, qc110_ss, qc101_ss, qc011_ss, qc100_sss, qc010_sss.  
Ltac unf_qd := try unfold  qd201, qd021, qd101_s, qd101_s, qd020_s, qd100_ss, qd100_ss,  qd121, qd111_s, qd120_s, qd210_s, qd110_ss, qd101_ss, qd011_ss, qd100_sss, qd010_sss. 
Ltac unf := try unf_phi; try unf_trm; try unf_qa ; try unf_qb; try unf_qc; try unf_qd.
