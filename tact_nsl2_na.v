Load "nsl2_na" .


(***********unfold****************)

Ltac unf_phi := try unfold phi0, phi1, phi2, phi3, phi4, phi21, phi22, phi23, phi24.

 (* try unfold  phi31, phi32, phi33, phi34, phi41, phi42, phi43, phi44.*)
Ltac unf_trm:=  try unfold  t12, t13,t14, t15 (*, t35, t45*).

Ltac unf_qa := try unfold  qa00, qa10, qa01; try unfold qa10_s, qa01_s; try unfold qa10_ss, qa01_ss; try unfold qa10_sss, qa01_sss ; try unfold qa22; try unfold qa20, qa11, qa02; try unfold qa20_s, qa11_s, qa02_s;  try unfold qa21,  qa12;  try unfold qa21_s,  qa12_s; try unfold qa20_ss, qa11_ss, qa02_ss.
 
Ltac unf_qb :=  try unfold qb22, qb21_s, qb12_s(* qb02_s*); try unfold qb20_ss, qb02_ss, qb11_ss, qb10_sss, qb01_sss.
(*Ltac unf_qc :=   try unfold qc21, qc20_s, qc11_s, qc02_s; try unfold qc10_ss, qc01_ss.
Ltac unf_qd :=   try unfold qd21, qd20_s, qd11_s, qd02_s; try unfold qd10_ss, qd01_ss.*)
Ltac unf := try unf_phi; try unf_trm; try unf_qa ; try unf_qb (*; try unf_qc; try unf_qd*).

