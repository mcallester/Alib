/** ========================================================================
Uses functions
========================================================================**/
where();
/***  {after 26 id_is_a_perm;}***/

clear_event(Schroeder_Bernstein);
/***  the event Schroeder_Bernstein is not present***/

exp_limit[0] = 200000;
/***  {36;done}***/

theorem Schroeder_Bernstein (
                             tau:type,
                             sigma:type,
                             inhabited(injection(sigma,tau)),
                             inhabited(injection(tau,sigma))){
  inhabited(bijection(tau,sigma))
  }{
  using(f:injection(sigma,tau),
        g:injection(tau,sigma),
        usef =mu assert(x:sigma){not(inhabited(preimage(x,g))) || exists(xx:usef){x = g(f(xx))}}, //would like to say is(x, g(some f(some usef)))
        h =def lambda(x:sigma){if(is(x,usef),f(x),the(y:tau){g(y)=x})}){
    show{is(h,surjection(sigma,tau))}{
      show(y:tau){inhabited(preimage(y,h))}{
        using(is(g(y),usef)){
          using(xx:assert(xx:usef){g(y) = g(f(xx))}){
            classify(f(xx));}};
        using(not(is(g(y),usef))){witness(g(y))}}};
    
    show{is(h,injection(sigma,tau))}{
      show(y:tau){unique(preimage(y,h))}{
        //follows if *either* x1 or x2 is usef
        show(x1:preimage(y,h),x2:preimage(y,h),is(x1,usef)){x1=x2}{
          show{is(x2,usef)}{
            suppose_not{classify(x1)}};};
        //follows when both are false
        show(x1:preimage(y,h),x2:preimage(y,h)){x1=x2}{
          using(not(is(x1,usef)),not(is(x2,usef)))}
        }};
    witness(h)}};
/***  {
    in 27 Schroeder_Bernstein;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_assume(inhabited(injection(sigma,tau)));
    4.show_assume(inhabited(injection(tau,sigma)));
    5.push_goal(inhabited(bijection(tau,sigma)));
    6.using_decl(f:injection(sigma,tau));
    7.using_decl(g:injection(tau,sigma));
    8.define(usef,
             mu(bound_s:subtype(sigma)){
               assert(bound_x:sigma){
                 or(not(inhabited(preimage(tau,sigma,bound_x,g))),
                    exists(bound_x_2:bound_s){
                      equal(bound_x,g(f(bound_x_2)))})}});
    9.define(h,
             lambda(bound_x:sigma){
               if(is(bound_x,usef),
                  f(bound_x),
                  the(assert(bound_x_2:tau){
                        equal(g(bound_x_2),bound_x)}))});
    10.proved(is(h,surjection(sigma,tau)));
    11.push_goal(is(h,injection(sigma,tau)));
    12.show_decl(y:tau);
    13.push_goal(unique(preimage(sigma,tau,y,h)));
    14.proved(forall(bound_x:assert(bound_x:sigma){equal(h(bound_x),y)},
                     bound_x_2:assert(bound_x_2:sigma){equal(h(bound_x_2),y)}){
                implies(is(bound_x,usef),
                        equal(bound_x,bound_x_2))});
    15.show_decl(x1:preimage(sigma,tau,y,h));
    16.show_decl(x2:preimage(sigma,tau,y,h));
    17.push_goal(equal(x1,x2));
    18.proved(implies(not(is(x1,usef)),
                      implies(not(is(x2,usef)),
                              equal(x1,x2))));
    19.push_backchain(equal(x1,x2));
    20.classifybb x1;
    21.classifybb x2;
    22.completed analyzing y;
    23.completed analyzing f;
    24.completed analyzing g;
    25.completed analyzing x1;
    26.completed analyzing x2;
    27.proof_failure;
    Failure to show equal(x1,x2);
    28.BREAKPOINT;}***/
