
/** ========================================================================
functions starts form initialization
========================================================================**/

load_mode[0] = 1;
/** {35;done} **/

declare_package(`functions);
/** {36;done} **/

clear_event(start_functions);
/** the event start_functions is not present **/

define start_functions true;
/** event 1 max 0 net 0 **/

/** ========================================================================

========================================================================**/
define preimage(sigma:type, tau:type, y:tau, f:sigma=>tau){
  assert(x:sigma){f(x)=y}};
/** event 2 max 354 net 354 **/

define injection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      unique(preimage(y,f))}}};
/** event 3 max 922 net 275 **/

theorem injection_thm1 (tau:type,sigma:type,
                          f:injection(tau,sigma), x_2:tau, x_3:tau, f(x_2)=f(x_3)){ 
  x_2=x_3}{
  classify(f(x_3)) //realize that f(x_3) has a unique preimage under f
  };
/** event 4 max 1825 net 221 **/

define surjection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      inhabited(preimage(y,f))}}};
/** event 5 max 1957 net 177 **/

define bijection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    is(f,injection(tau,sigma)) && is(f,surjection(tau,sigma))}};
/** event 6 max 2348 net 122 **/

theorem bijections_exist(sigma:type,tau:type){
  inhabited(bijection(sigma,tau))};
/** event 7 max 2535 net 29 **/

define bij_inverse(tau:type,sigma:type,f:bijection(sigma,tau)){
  the(g:tau=>sigma){forall(x:sigma){g(f(x))=x}}};
/** event 8 max 2939 net 613 **/

theorem bij_inverse_thm1(tau:type,sigma:type,f:bijection(sigma,tau)){
  is(bij_inverse(f),bijection)};
/** event 9 max 3585 net 120 **/

define composition(sigma:type,tau:type,gamma:type,f:tau=>gamma,g:sigma=>tau){lambda(x:sigma){f(g(x))}};
/** event 10 max 9597 net 289 **/

define id_fun(s:type){lambda(x:s){x}};
/** event 11 max 34 net 34 **/

theorem bij_inverse_thm2 (s:type,u:type,f:bijection(s,u)){
  composition(bij_inverse(f),f) = id_fun(s) && composition(f,bij_inverse(f)) = id_fun(u)};
/** event 12 max 5263 net 610 **/

event_name(current_event[0])
/** {37;bij_inverse_thm2} **/

define permutation(sigma:type){bijection(sigma,sigma)};
/** event 13 max 111 net 111 **/

theorem permutation_thm1 (s:type,f:permutation(s),g:permutation(s)){is(composition(f,g),permutation(s))};
/** event 14 max 432 net 432 **/

theorem permutation_thm2(s:type,f:permutation(s)){composition(f,bij_inverse(f)) = id_fun(s)};
/** event 15 max 317 net 97 **/

define associative(s:type){
  assert(f:s=>s=>s){
    forall(x:s,y:s,z:s){
      f(x,f(y,z))=f(f(x,y),z)}}};
/** event 16 max 1007 net 437 **/
