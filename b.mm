$c THEORIE $.

$( lettres, lettres prim'ees et lettres diff'erentes $)

$[ lettres.mm $]
$c SIGNE THEORIE SIGNE_LOGIQUE SIGNE_SPECIFIQUE $.

$( Les signes sp'ecifiques seront de poids 2. TODO : g'en'eraliser aux signes de poids n (cela n'ecessite d'avoir des entiers inuitifs et des listes). $)

${

$v sl $.
tsl $f SIGNE_LOGIQUE sl $.
ax-signe_logique_SIGNE $a SIGNE sl $.
$}
$c tau \/ -. $.

${
s_tau $a SIGNE_LOGIQUE tau $.
s_or $a SIGNE_LOGIQUE \/ $.
s_not $a SIGNE_LOGIQUE -. $.
$}

${
$v l_ $.
vl $f LETTRE l_ $.
lprime $a LETTRE l_ ' $.

ax-signe_lettre $a SIGNE l_ $.
$}

$c ASSEMBLAGE $.
${
$v signe $.
ts $f SIGNE signe $.
df_asssemblage_signe $a ASSEMBLAGE signe $.
$}

${
$v u_ v_ $.
vu $f ASSEMBLAGE u_ $.
vf $f ASSEMBLAGE v_ $.
df-asssemblage_concat $a ASSEMBLAGE u_ v_ $.
$}

$(
${
$v A_ B_ $.
tA $f ASSEMBLAGE A_ $.
tBB $f ASSEMBLAGE B_ $.
exemple_assemblage $p ASSEMBLAGE \/ A_ -. B_ $= ( s_or ax-signe_logique_SIGNE df_asssemblage_signe s_not df-asssemblage_concat ) CDEAFDEBGGG $.
$}
$)


$c ( ) $.

${
$v A_ x_ y_ $.
tx $f LETTRE x_ $.
ty $f LETTRE y_ $.
df-assemblage_tau.tA $f ASSEMBLAGE A_ $.

df-assemblage_tau $a ASSEMBLAGE tau x_ ( A_ ) $.
$}

$( Lettre ne figurant pas dans un assemblage. $)
$c NOTIN $.
${
$v l_ l_' $.
ax-ne_figure_pas_diff.tl  $f LETTRE l_ $.
ax-ne_figure_pas_diff.tl. $f LETTRE l_' $.
ax-ne_figure_pas_diff.1   $e DIFF l_ l_' $.
ax-ne_figure_pas_diff     $a NOTIN l_ l_' $.
$}

${
$v l_ u_ v_ $.
ax-ne_figure_pas_concat.tu $f ASSEMBLAGE u_ $.
ax-ne_figure_pas_concat.tv $f ASSEMBLAGE v_ $.
ax-ne_figure_pas_concat.tl $f LETTRE l_ $.
ax-ne_figure_pas_concat.1 $e NOTIN l_ u_ $.
ax-ne_figure_pas_concat.2 $e NOTIN l_ v_ $.
ax-ne_figure_pas_concat $a NOTIN l_ u_ v_ $.
$}

${
$v x_ A_ $.
ax-ne_figure_pas_tau.tx $f LETTRE x_ $.
ax-ne_figure_pas_tau.tA $f ASSEMBLAGE A_ $.
ax-ne_figure_pas_tau $a NOTIN x_ tau ( x_ ) A_ $.
$}

${
$v x_ y_ A_ $.
ax-ne_figure_pas_tau_diff.tx $f LETTRE x_ $.
ax-ne_figure_pas_tau_diff.ty $f LETTRE y_ $.
ax-ne_figure_pas_tau_diff.tA $f ASSEMBLAGE A_ $.
ax-ne_figure_pas_tau_diff.1 $e DIFF x_ y_ $.
ax-ne_figure_pas_tau_diff.2 $e NOTIN x_ A_ $.
ax-ne_figure_pas_tau_diff $a NOTIN x_ tau ( y_ ) A_ $.
$}

${
$( exemple $)
 exemple $p ASSEMBLAGE tau x ' ( x ' \/ x ' ) $= ( lx lprime ax-signe_lettre df_asssemblage_signe s_or ax-signe_logique_SIGNE df-asssemblage_concat df-assemblage_tau ) ABZICDZEFDJGGH $.
$}

$( Identique $)

$( CM indique que la r`egle est un crit`ere metalogique justifiant les identit'es $)

$c CM =^= $.
${
$v A_ B_ $.
ax-id_refl.tA $f ASSEMBLAGE A_ $.
tB $f LETTRE B_ $.
ax-id_refl $a CM A_ =^= A_ $.
$}

${
$v A_ B_ $.
df-id_sym.tA $f ASSEMBLAGE A_ $.
df-id_sym.tB $f ASSEMBLAGE B_ $.
df-id_sym.1 $e CM A_ =^= B_ $.
df-id_sym $a CM B_ =^= A_ $.
$}

${
$v A_ B_ C_ $.
df-id_trans.tA $f ASSEMBLAGE A_ $.
df-id_trans.tB $f ASSEMBLAGE B_ $.
df-id_trans.tC $f ASSEMBLAGE C_ $.

h1 $e CM A_ =^= B_ $.
h2 $e CM B_ =^= C_ $.
df-id_trans $a CM A_ =^= C_ $.
$}

${
$v A_ $.
ax-id_par.tA $f ASSEMBLAGE A_ $.
ax-id_parr $a CM A_ =^= ( A_ ) $.
ax-id_parl $a CM ( A_ ) =^= A_ $.
$}

$( Reference `a une ou deux m'etalettres (pr'esentes ou non) dans un assemblage $)
$c [ ] , $.

${
$v A_ x_ y_ $.
ax-id_var.tA $f ASSEMBLAGE A_ $.
ax-id_var.tx $f LETTRE x_ $.
ax-id_var.ty $f LETTRE y_ $.
ax-id_var $a CM A_ =^= ( A_ [ x_ ] ) $.
ax-id_var2 $a CM A_ =^= ( A_ [ x_ , y_ ] ) $.
$}

$( Substitution $)
$c | $.
${
$v A_ B_ x_ $.
df-sub.tA $f ASSEMBLAGE A_ $.
df-sub.tB $f ASSEMBLAGE B_ $.
df-sub.tx $f LETTRE x_ $.
df-sub $a ASSEMBLAGE ( B_ | x_ ) A_ $.
$}

${
$v B_ x_ A_ $.
ax-sub_sans_lettre.tA $f ASSEMBLAGE A_ $.
ax-sub_sans_lettre.tB $f ASSEMBLAGE B_ $.
ax-sub_sans_lettre.tx $f LETTRE x_ $.
ax-sub_sans_lettre.lettre_ne_figure_pas_assemblage $e CM x_ NOTIN A_ $.
ax-sub_sans_lettre $a ( B_ | x_ ) A_ =^= A_ $.
$}

${
$v B_ x_ sl $.
ax-sub.tsl $f SIGNE_LOGIQUE sl $.
ax-sub.tB $f ASSEMBLAGE B_ $.
ax-sub.tx $f LETTRE x_ $.
ax-sub_signe_logique $a CM ( B_ | x_ ) sl =^= sl $.
ax-sub_lettre_eg $a CM ( B_ | x_ ) x_ =^= B_ $.
$}

${
$v A_ A_' B_ x_ $.
ax-sub_sub.tA. $f ASSEMBLAGE A_ $.
ax-sub_sub.tA $f ASSEMBLAGE A_' $.
ax-sub_sub.tB $f ASSEMBLAGE B_ $.
ax-sub_sub.tx $f LETTRE x_ $.
ax-sub_sub.1 $e CM A_ =^= A_' $.
ax-sub_sub $a CM ( B_ | x_ ) A_ =^= ( B_ | x_ ) A_' $.
$}

${
$v B_ x_ y_ $.
ax-sub_lettre_diff.tB $f ASSEMBLAGE B_ $.
ax-sub_lettre_diff.tx $f LETTRE x_ $.
ax-sub_lettre_diff.ty $f LETTRE y_ $.
$( Ici , la tentation est grande de sp'ecifier simplement $d x_ y_ $. Malheureusement, cela ne peut marcher car une fois substitu'es par des vraies lettres (constantes), la condition de variables disjointes ne s'applique plus. $)
ax-sub_lettre_diff.x_y_diff $e DIFF x_ y_ $.
ax-sub_lettre_diff $a CM ( B_ | x_ ) y_ =^= y_ $.
$}

${
$v B_ x_ u_ v_ u_' v_' $.
ax-sub_concat.tB $f ASSEMBLAGE B_ $.
ax-sub_concat.tx $f LETTRE x_ $.
ax-sub_concat.tu $f ASSEMBLAGE u_ $.
ax-sub_concat.tv $f ASSEMBLAGE v_ $.
ax-sub_concat.tu. $f ASSEMBLAGE u_' $.
ax-sub_concat.tv. $f ASSEMBLAGE v_' $.
ax-sub_concat.hu. $e CM u_' =^= ( B_ | x ) u_ $.
ax-sub_concat.hv. $e CM v_' =^= ( B_ | x ) v_ $.
ax-sub_concat $a CM ( B_ | x_ ) ( u_ v_ ) =^= ( u_' v_' ) $.
$}

${
$v B_ x_ A_ $.
ax-sub_tau_eg.tB $f ASSEMBLAGE B_ $.
ax-sub_tau_eg.tx $f LETTRE x_ $.
ax-sub_tau_eg.tA $f ASSEMBLAGE A_ $.
ax-sub_tau_eg $a CM ( B_ | x_ ) ( tau x_ ( A_ ) ) =^= tau x_ ( A_ ) $.
$}

${
$v B_ A_ A_' x_ y_ $.
ax-sub_tau_diff.tB $f ASSEMBLAGE B_ $.
ax-sub_tau_diff.tx $f LETTRE x_ $.
ax-sub_tau_diff.ty $f LETTRE y_ $.
$( Ici , la tentation est grande de sp'ecifier simplement $d x_ y_ $. Malheureusement, cela ne peut marcher car une fois substitu'es par des vraies lettres (constantes), la condition de variables disjointes ne s'applique plus. $)
ax-sub_tau_diff.x_y_diff $e DIFF x_ y_ $.
ax-sub_tau_diff.tA $f ASSEMBLAGE A_ $.
ax-sub_tau_diff.tA. $f ASSEMBLAGE A_' $.
ax-sub_tau_diff.hA. $e CM ( B_ | x_ ) A_ =^= A_' $.
ax-sub_tau_diff $a CM ( B_ | x_ ) ( tau y_ ( A_ ) ) =^= tau y_ ( A_' ) $.
$}

${
$v B_ x_ A_ $.
df-subst.tB $f ASSEMBLAGE B_ $.
df-subst.tx $f LETTRE x_ $.
df-subst.tA $f ASSEMBLAGE A_ $.
df-subst $a CM A_ [ B_ ] =^= ( B_ | x_ ) A_ $.
$}

${
$v A_ B_ C_ x_ y_ x_' y_' $.
df-subst2.tx $f LETTRE x_ $.
df-subst2.ty $f LETTRE y_ $.
df-subst2.tx. $f LETTRE x_' $.
df-subst2.ty. $f LETTRE y_' $.
df-subst2.tA $f ASSEMBLAGE A_ $.
df-subst2.tB $f ASSEMBLAGE B_ $.
df-subst2.tC $f ASSEMBLAGE C_ $.

$( Lettres toutes diff'erentes entre elles. $)
$( Ici , la tentation est grande de sp'ecifier simplement $d x__ y_ x__' y_' $. Malheureusement, cela ne peut marcher car une fois substitu'es par des vraies lettres (constantes), la condition de variables disjointes ne s'applique plus. $)
df-subst2.1 $e DIFF x_ y_ $.
df-subst2.2 $e DIFF x_ x_' $.
df-subst2.3 $e DIFF x_ y_' $.
df-subst2.4 $e DIFF y_ x_' $.
df-subst2.5 $e DIFF x_ y_' $.
df-subst2.6 $e DIFF x_' y_' $.

df-subst2.7 $e NOTIN x_' A_ $.
df-subst2.8 $e NOTIN x_' B_ $.
df-subst2.9 $e NOTIN x_' C_ $.

df-subst2.10 $e NOTIN y_' A_ $.
df-subst2.11 $e NOTIN y_' B_ $.
df-subst2.12 $e NOTIN y_' C_ $.

df-subst2 $a CM ( A_ [ B_ , C_ ] ) =^= ( ( B_ | x_' ) ( C_ | y_' ) ( x_' | x_ ) ( y_' | y_ ) A_ ) $.
$}

$( CS1 $)
${
$v B_ A_ x_ x_' $.
cs1.tx $f LETTRE x_ $.
cs1.tx. $f LETTRE x_' $.
cs1.tA $f ASSEMBLAGE A_ $.
cs1.tB $f ASSEMBLAGE B_ $.
$( Ici , la tentation est grande de sp'ecifier simplement $d x_'A_ $. Malheureusement, cela ne peut marcher car une fois substitu'es par des vraies lettres (constantes), la condition de variables disjointes ne s'applique plus. $)
cs1.ne_figure_pas $e NOTIN x_' A_ $.
cs1 $a CM ( B_ | x_ ) A_ =^= ( B_ | x_' ) ( x_' | x_ ) A_ $.
$}

$( Sans utiliser cs1 et sans crit`eres sur x et x', on montre (B|x)x = (B|x')(x'|x)x $)
${
$v B_ x_ x_' $.
cs1_sans_critere_lettre.tB $f ASSEMBLAGE B_ $.
cs1_sans_critere_lettre.tx $f LETTRE x_ $.
cs1_sans_critere_lettre.tx. $f LETTRE x_' $.
cs1_sans_critere_lettre $p CM ( B_ | x_ ) x_ =^= ( B_ | x_' ) ( x_' | x_ ) x_ $= ( ax-signe_lettre df_asssemblage_signe df-sub ax-sub_lettre_eg df-id_sym df-id_trans ax-sub_sub ) BDEZABFZCDEZACFZKMBFZACFLANABGNAACGHIMOACOMMBGHJI $.

$}

$( Avec le crit`ere x <>x', on peut utiliser cs1 $)
${
$v B_ x_ x_' $.
cs1_lettre.tB $f ASSEMBLAGE B_ $.
cs1_lettre.tx $f LETTRE x_ $.
cs1_lettre.tx. $f LETTRE x_' $.
cs1_lettre.1 $e DIFF x_' x_ $.
cs1_lettre $p CM ( B_ | x_ ) x_ =^= ( B_ | x_' ) ( x_' | x_ ) x_ $= ( ax-signe_lettre df_asssemblage_signe ax-ne_figure_pas_diff cs1 ) BCBEFACBDGH $.
$}

$( CS2 $)
${
$v A_ B_ C_ C_' x_ y_ $.
cs2.tA $f ASSEMBLAGE A_ $.
cs2.tB $f ASSEMBLAGE B_ $.
cs2.tC $f ASSEMBLAGE C_ $.
cs2.tC. $f ASSEMBLAGE C_' $.
cs2.tx $f LETTRE x_ $.
cs2.ty $f LETTRE y_ $.
cs2.1 $e DIFF x_ y_ $.
cs2.2 $e NOTIN y_ B_ $.
cs2.3 $e CM C_' =^= ( B_ | x_ ) C_ $.
cs2 $a ( B  | x_ ) ( C | y_ ) A_ =^= ( C_' | y ) ( B_ | x_ ) A_ ) $.
$}

$( CS3 $)
${
$v A_ A_' x_ x_' $.
cs3.tA $f ASSEMBLAGE A_ $.
cs3.tA. $f ASSEMBLAGE A_' $.
cs3.tx $f LETTRE x_ $.
cs3.tx. $f LETTRE x_' $.
cs3.1 $e NOTIN x_' A_ $.
cs3.2 $e CM A_' =^= ( x_' | x_ ) A_ $.
cs3 $a tau x_ ( A_ ) =^= tau x_' ( A_' ) $.
$}

$( CS4 CS5 TODO $)

$( 3. Constructions formatives $)
$c PREMIERE_ESPECE DEUXIEME_ESPECE $.
${
$v A_ B_ $.
cf1.tA $f ASSEMBLAGE A_ $.
cf1.tB $f ASSEMBLAGE B_ $.
cf1.1 $e CM A_ =^= tau B_ $.
cf1 $a PREMIERE_ESPECE A_
$}

${
$v A_ B_ x_ $.
cf2.tA $f ASSEMBLAGE A_ $.
cf2.tB $f ASSEMBLAGE B_ $.
cf2.tx $f LETTRE x_ $.
cf2.1 $e CM A_ =^= tau ( x_ ) B_ $.
cf2 $a PREMIERE_ESPECE A_
$}

$( Premi`ere esp`ece : lettre ou tau $)
${
$v A_ x_ $.
cf3.tA $f ASSEMBLAGE A_ $.
cf3.tx $f LETTRE x_ $.
$( Ici on utilise l'équivalence =^= pour les cas (x) $)
cf3.1 $e CM A_ =^= x_ $.
cf3 $a PREMIERE_ESPECE A_
$}


${ Deuxi`eme esp`ece : ou, non, signe spécifique $)

${
$v T_ A_ B_ $.
cf4.tT $f THEORIE T_ $.
cf4.tA $f ASSEMBLAGE A_ $.
cf4.tB $f ASSEMBLAGE B_ $.
cf4.1 $e CM A_ =^= \/ B_ $.
cf4 $a DEUXIEME_ESPECE A_
$}

${
$v T_ A_ B_ $.
cf5.tT $f THEORIE T_ $.
cf5.tA $f ASSEMBLAGE A_ $.
cf5.tB $f ASSEMBLAGE B_ $.
cf5.1 $e CM A_ =^= -. B_ $.
cf5 $a DEUXIEME_ESPECE T_ A_
$}


${
$v A_ T_ s_ $.
cf6.tA $f ASSEMBLAGE A_ $.
cf6.tT $f THEORIE T_ $.
cf6.ts $f SIGNE_SPECIFIQUE T_ s_ $.
cf6.1 $e CM A_ =^= s_ B_ $.
cf6 $a DEUXIEME_ESPECE T_ A_
$}

$( Construction formative $)
$c CONSTRUCTION_FORMATIVE $.
${
$v T_ x_ $.
ax-cfa.tx $f LETTRE x_ $.
ax-cfa.tT $f THEORIE T_ $.
ax-cfa $a CONSTRUCTION_FORMATIVE T_ x_ $.
$}

${
$v T_ A_ B_ $.
ax-cfb.tT $f THEORIE T_ $.
ax-cfb.tA $f ASSEMBLAGE A_ $.
ax-cfb.1 $e DEUXIEME_ESPECE T_ B_ $.
ax-cfb.2 $e CM A_ =^= -. B_ $.
ax-cfb $a CONSTRUCTION_FORMATIVE T_ A_ $.
$}

${
$v T_ A_ B_ C_ $.
ax-cfc.tT $f THEORIE T_ $.
ax-cfc.tA $f ASSEMBLAGE A_ $.
ax-cfc.tB $f ASSEMBLAGE B_ $.
ax-cfc.1 $e DEUXIEME_ESPECE T_ A_ $.
ax-cfc.2 $e DEUXIEME_ESPECE T_ B_ $.
ax-cfc.3 $e CM A_ =^= \/ B_ C_ $.
ax-cfc $a CONSTRUCTION_FORMATIVE T_ A_ $.
$}

$( Par. 2. Thi'eor`emes $)
$c ou $.

${
$v A_ B_ T_ $.
df-ou.tA $f ASSEMBLAGE A_ $.
df-ou.tB $f ASSEMBLAGE B_ $.
df-ou.tT $f THEORIE  T_ $.
df-ou.1 $e RELATION A_ T_ $.
df-ou.2 $e RELATION B_ T_ $.
df-ou $a ( A_ ) ou ( B_ ) =^= \/ A_ B_ $.
$}

$( Par. 3. Th'eories logiques $)
$c THEORIE_LOGIQUE $.
$c S1 S2 S3 S4 $.

${
s1.tA $f ASSEMBLAGE A_ $.
s1.tT $f THEORIE_LOGIQUE T_ $.
s1.1 $e RELATION T_ A_ $.
s1 $a AXIOME T_ ( A ou A ) \imply A $.
$}

${
$v T_ $.
schema_s1.tT $f THEORIE T_ $.
schema_s1.1 $e THEORIE_LOGIQUE T_ $.
schema_s1 $a SCHEMA S1 T_ $.

$}
$( C27 $)
${
$v R_ T_ x_ $.
c27.tR $f ASSEMBLAGE R_ $.
c27.tT $f THEORIE T_ $.
c27.tx $f LETTRE x_ $.
c27.1 $e THEORIE_LOGIQUE T_ $.
c27.2 $e RELATION T_ R_  $.
c27.3 $e NON_CONSTANTE x_ T_ $.
c27 $a THEOREME T_ ( forall x_ ) R_  $.
$}
