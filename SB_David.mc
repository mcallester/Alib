reinitialize();
/** after 0 initialization; **/

declare_package(`schroeder_bernstein_functions);

clear_event(start_SB);
/** the event start_SB is not present **/

define start_SB true;
/** event 1 max 0 net 0 **/

/** ========================================================================
empty set exists
========================================================================**/

check_for_corruption[0] = 1;

proof_stepping[0] = 0;

intern_stepping[0] = 0;

current_events[0]

break_on_user_error[0] = 0;

break_on_proof_failure[0]=0;

clear_event(sets_exist);
/** the event sets_exist is not present **/

theorem sets_exist (foo:type){inhabited(set_of(foo))};
/** event 2 max 25 net 24 **/

clear_event(test1);
/** the event test1 is not present **/

theorem test1(tau:type){forall(x:assert(xx:tau){not(equal(xx,xx))}){false}};

clear_event(test2);
/** the event test2 is not present **/

theorem test2(tau:type){forall(x:assert(xx:tau){not(equal(xx,xx))}){not(is(x,tau))}}{
  suppose_not;
};

clear_event(emptyset_exists);
/** the event emptyset_exists is not present **/

theorem emptyset_exists(tau:type){exists(s:set_of(tau)){empty(in(s))}
  }{
  using(emptyset=the_set(x:tau){not(x=x)}){
    show{empty(in(emptyset))};
    witness(emptyset)}
  };
/** event 20 max 412 net 288 **/

int x[0]=1;

/** ========================================================================
//do the next two the first time

//int intern_hook_count[0]=0;

//set_intern_hook(mze){if(mze->constructor==conservative){intern_hook_count[0]++;}};
//set_intern_hook(mze){intern_hook_count[0]++;};

//do the next two the second time (after clearing preimage).

//int num_desired[0]=10;

//set_intern_hook(mze){
  //  if(intern_hook_count[0] && (random()%intern_hook_count[0])<num_desired[0]){
    //    mcpprint(sugar(mze));}
  //  };
========================================================================**/

clear_event(preimage);
/** the event preimage is not present **/

define preimage(tau:type, sigma:type, y:sigma, h:tau=>sigma){
  assert(x:tau){h(x)=y}};
/** event 4 max 2245 net 2245 **/

int_exp(max_total[0])

clear_event(injection);
/** the event injection is not present **/

define injection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      unique(preimage(y,f))}}};
/** event 5 max 2192 net 2192 **/

int_exp(max_total[0])

define surjection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      inhabited(preimage(y,f))}}};
/** event 6 max 3381 net 1548 **/

int_exp(max_total[0])

clear_event(bijection);
/** the event bijection is not present **/

define bijection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    is(f,injection(tau,sigma)) && is(f,surjection(tau,sigma))}};
/** event 7 max 4482 net 886 **/

int_exp(max_total[0])

clear_event(bijections_invert);
/** the event bijections_invert is not present **/


theorem bijections_invert(tau:type,sigma:type,inhabited(bijection(tau,sigma))){
  inhabited(bijection(sigma,tau))
  }{
  using(
        f:bijection(tau,sigma),
        g = lambda(x:sigma){the(y:tau){f(y)=x}}){
        //intern_cps(lambd(x:sigma){...})
        ///decl(x:sigma)
        ////intern_cps(the(assert(y:tau){f(y)=x}))
        
        /////backchain(inhabited(assert(...)))
        //////analyze(inhabited(...))
        ///////classify(f) binds a surjection variable to f
        ///////yields forall(y:tau)exists(x:sigma)f(x)=y
        ///////yields exists(x:sigma)f(x)=y
        ///////yields the backchain goal.
        
        /////backchain(unique(assert(...)))
        //////analyze(unique(...))
        ///////classify(f) binds an injection variable to f.
        ///////yields forall(y:sigma){unique(assert(x:tau){f(x) = y})}
        ///////yields unique(x:sigma)f(x)=y
        ///////yields the backchain goal.
        
        
        //analyze(g)
        ///classify(f) generates the desired habitation and uniquenes formulas
        //    A.forall(x:sigma){inhabited(preimage(x,f))}
        //    B.forall(x:sigma){unique(preimage(x,f))}
        //    C.f:tau=>sigma
        //classify(g) then places g under bijection which proves the goal.
        //    1.show(forall(x:tau){inhabited(preimage(x,[g@mvar:sigma=>tau]))})
        //    2.show(forall(x:tau){unique(preimage(x,[g@mvar:sigma=>tau]))}
        //    3.show(inhabited(preimage(gvar(tau),[g@mvar:sigma=>tau]))
        //    4.show(unique(preimage(gvar(tau),[g@mvar:sigma=>tau]))
        //    5.show(inhabited(assert(y:sigma){[g@mvar:sigma=>tau](y)=gvar(tau)}))  //step1: create gvar(sigma)
        //    6.show(unique(assert(y:sigma){[g@mvar:sigma=>tau](y)=gvar(tau)}))
        //    7.show(inhabited(assert(y:sigma){the(z:tau){f(z)=y}=gvar(tau)}))
        //    8.show(unique(assert(y:sigma){the(z:tau){f(z)=y}=gvar(tau)}))

        //    9.the(z:tau){f(z)=f(gvar(tau))} = gvar(tau)    //using existential witness f(gvar(tau))

        //the(z:tau){f(z)=y}=gvar(tau)  iff  y=f(gvar(tau)) && gvar(tau):tau

        //11.the(z:rho){phi[y,z]}=c iff (phi[y,c] && c:rho)    //step2: alternative matrix for goal

        //(renamed x to y)

        //13.show(exists(y:sigma){y=f(gvar(tau))})  //step3: notice this silly kind of existential goal somehow
        //14.show(unique(assert(y:sigma){y=f(gvar(tau))}))
        //15.show(is(f(gvar(tau)),sigma))  //done  eg from f(gvar(tau)) = f(gvar(tau))

                                    show(z:tau){inhabited(preimage(z,g))}{classify(f(z))};

                                    witness(g)
                                    }};
/** event 8 max 11494 net 3004 **/

int_exp(max_total[0])

clear_event(empty_uniqueness);
/** the event empty_uniqueness is not present **/

theorem empty_uniqueness (tau:type) {
  unique(assert(s:set_of(tau)){empty(in(s))})}{
  show(x1:assert(s:set_of(tau)){empty(in(s))},
       x2:assert(s:set_of(tau)){empty(in(s))}){
    x1=x2}};
/** event 9 max 211 net 13 **/

clear_event(test_injectivity);
/** the event test_injectivity is not present **/

theorem test_injectivity (tau:type,sigma:type,
                          f:injection(tau,sigma), x_2:tau, x_3:tau, f(x_2)=f(x_3)){ 
  x_2=x_3}{
  classify(f(x_3)) //realize that f(x_3) has a unique preimage under f
  };
/** event 10 max 16486 net 1074 **/

clear_event(Schroeder_Bernstein);
/** the event Schroeder_Bernstein is not present **/

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
        h = lambda(x:sigma){if(is(x,usef),f(x),the(y:tau){g(y)=x})}){
    show{is(h,surjection(sigma,tau))}{
      show(y:tau){inhabited(preimage(y,h))}{
        using(is(g(y),usef)){
          using(xx:assert(xx:usef){g(y) = g(f(xx))}){
            classify(f(xx));}};
        using(not(is(g(y),usef))){witness(g(y))}}};
    
    show{is(h,injection(sigma,tau))}{
      show(y:tau){unique(preimage(y,h))}{
        show(x1:preimage(y,h),x2:preimage(y,h),is(x1,usef)){x1=x2}{
          show{is(x2,usef)}{
            suppose_not{classify(x1)}};};
        show(x1:preimage(y,h),x2:preimage(y,h)){x1=x2}{
          show(not(is(x1,usef))){not(is(x2,usef))}{
            suppose_not}};}};
    witness(h)}};
/** event 11 max 30803 net 552 **/
