
restart_event(`schroeder_bernstein_taxonomic);
/** {36;done} **/

declare_package(`schroeder_bernstein_taxonomic);
/** {37;done} **/

/** ========================================================================
empty set exists
========================================================================**/

clear_event(emptytype_exists)
/** emptytype_exists has not been defined as an event **/

theorem emptytype_exists{
  exists(tau:type){empty(tau)}}{
  using(sigma:type){classify(assert(x:sigma){not(x=x)})}  
  };
/** {38;done} **/

finish_event();
/** there is no suspended event to finish **/

define unique_type(s:type, y:s){
  assert(x:s){x=y}};
/** {39;done} **/

define preimage(s:type, w:type, y:w, h:s=>w){
  apply_some(fun_relation(h), unique_type(y))};
/** {40;done} **/

//is(x,apply_some(R,tau))

//unique(apply_some(R,tau))


int_exp(max_total[0])
/** {41;498} **/

define injection(s:type,w:type){
  assert(f:s=>w){
    forall(y:w){
      unique(preimage(y,f))}}};
/** {42;done} **/

int_exp(max_total[0])
/** {43;1124} **/

define surjection(s:type,w:type){
  assert(f:s=>w){
    forall(y:w){
      inhabited(preimage(y,f))}}};
/** {44;done} **/

int_exp(max_total[0])
/** {45;1123} **/

define bijection(s:type,w:type){
  assert(f:s=>w){
    is(f,injection(s,w)) && is(f,surjection(s,w))}};
/** {46;done} **/

int_exp(max_total[0])
/** {47;1087} **/

//RUNS TO HERE

exp_limit[0]=500000;
/** {48;done} **/

clear_event(bijections_invert);
/** bijections_invert has not been defined as an event **/
proof_stepping[0]=0;
/** {49;done} **/

theorem bijections_invert(s:type, w:type, inhabited(bijection(s,w))){
  inhabited(bijection(w,s))
  }{
  using(f:bijection(s,w),
        g = lambda(x:w){the(preimage(x,f))}){
    witness(g)}};
/** {
    in event bijections_invert;
    1.show_decl(s:type);
    2.show_decl(w:type);
    3.show_assume(inhabited(bijection(s,w)));
    4.push_goal(inhabited(bijection(w,s)));
    5.using_decl(f:bijection(s,w));
    6.define(g,
             lambda(bound_x:w){
               the(preimage(s,w,bound_x,f))});
    completed analyzing s;
    completed analyzing w;
    completed analyzing inhabited(bijection(w,s));
    goal failed,looping step of classifying g;
    7.classifying g;
    8.analyzing s;
    goal not achieved;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/

step();
/** {
    in event bijections_invert;
    1.show_decl(s:type);
    2.show_decl(w:type);
    3.show_assume(inhabited(bijection(s,w)));
    4.push_goal(inhabited(bijection(w,s)));
    5.using_decl(f:bijection(s,w));
    6.define(g,
             lambda(bound_x:w){
               the(preimage(s,w,bound_x,f))});
    completed analyzing s;
    completed analyzing w;
    completed analyzing inhabited(bijection(w,s));
    goal failed,looping step of classifying g;
    7.classifying g;
    completed analyzing s;
    8.analyzing w;
    goal not achieved;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/

step();
/** {
    in event bijections_invert;
    1.show_decl(s:type);
    2.show_decl(w:type);
    3.show_assume(inhabited(bijection(s,w)));
    4.push_goal(inhabited(bijection(w,s)));
    5.using_decl(f:bijection(s,w));
    6.define(g,
             lambda(bound_x:w){
               the(preimage(s,w,bound_x,f))});
    completed analyzing s;
    completed analyzing w;
    completed analyzing inhabited(bijection(w,s));
    goal failed,looping step of classifying g;
    7.classifying g;
    completed analyzing s;
    completed analyzing w;
    8.analyzing f;
    goal not achieved;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/

step();
/** {
    in event bijections_invert;
    1.show_decl(s:type);
    2.show_decl(w:type);
    3.show_assume(inhabited(bijection(s,w)));
    4.push_goal(inhabited(bijection(w,s)));
    5.using_decl(f:bijection(s,w));
    6.define(g,
             lambda(bound_x:w){
               the(preimage(s,w,bound_x,f))});
    completed analyzing s;
    completed analyzing w;
    completed analyzing inhabited(bijection(w,s));
    goal failed,looping step of classifying g;
    7.classifying g;
    completed analyzing s;
    completed analyzing w;
    completed analyzing f;
    8.analyzing g;
    goal not achieved;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/


types_of(g)
/** {
    50;
    1:lambda(bound_s:type){
      assert(bound_fun:arrow([w@type#1],bound_s)){
        forall(bound_x:bound_s){
          unique(preimage([w@type#1],
                          bound_s,
                          bound_x,
                          bound_fun))}}}([s@type#0]);
    2:lambda(bound_s:type){
      assert(bound_fun:arrow(w,bound_s)){
        forall(bound_x:bound_s){
          unique(preimage(w,bound_s,bound_x,bound_fun))}}}([s@type#0]);
    3:pi(bound_x:w){preimage(s,w,bound_x,f)};
    4:arrow([w@type#1],s);
    5:injection(w,[s@type#0]);
    6:assert(bound_fun:arrow(w,[s@type#0])){
      forall(bound_x:[s@type#0]){
        unique(preimage(w,
                        [s@type#0],
                        bound_x,
                        bound_fun))}};
    7:injection([w@type#1],[s@type#0]);
    8:assert(bound_fun:arrow([w@type#1],[s@type#0])){
      forall(bound_x:[s@type#0]){
        unique(preimage([w@type#1],
                        [s@type#0],
                        bound_x,
                        bound_fun))}};
    9:arrow(w,s);
    10:injection(w,s);
    11:assert(bound_fun:arrow(w,s)){
      forall(bound_x:s){
        unique(preimage(w,s,bound_x,bound_fun))}};
    12:arrow(w,[s@type#0]);
    13:arrow([w@type#1],[s@type#0]);} **/

types_of(f)
/** {
    51;
    1:bijection(s,w);
    2:arrow(s,w);
    3:arrow([s@type#0],[w@type#1]);
    4:arrow(s,[w@type#1]);
    5:bijection([s@type#0],[w@type#1]);} **/

int_exp(intern_exp(`{is(g,bijection(w,s))})->show)
/** {52;1} **/

int_exp(intern_exp(`{is([g@arrow(w,s)#0],injection(w,s)) && is([g@arrow(w,s)#0],surjection(w,s))})->show)
/** {53;1} **/

pointer_exp(intern_exp(`{is([g@arrow(w,s)#0],injection(w,s)) && is([g@arrow(w,s)#0],surjection(w,s))})->truth_justification)
/** {54;(nil)} **/

pointer_exp(intern_exp(`{is([g@arrow(w,s)#0],surjection(w,s))})->truth_justification)
/** {55;(nil)} **/

pointer_exp(intern_exp(`{is([g@arrow(w,s)#0],injection(w,s))})->truth_justification)
/** {56;0x55557e63e354} **/

int_exp(intern_exp(`{is([g@arrow(w,s)#0],surjection(w,s))})->show)
/** {57;1} **/

int_exp(intern_exp(`{forall(yy:s){inhabited(preimage(yy,[g@arrow(w,s)#0]))}})->show)
/** {58;1} **/

int_exp(intern_exp(`{inhabited(preimage([mvar:s#0],[g@arrow(w,s)#0]))})->show)
/** {59;1} **/

class_of(preimage([mvar:s#0],[g@arrow(w,s)#0]))
/** {
    62;
    1:assert(bound_x:w){
      exists(bound_x_2:unique_type(s,[mvar:s#0])){
        and(is(bound_x_2,s),
            fun_relation([g@arrow(w,s)#0])(bound_x,bound_x_2))}};
    2:assert(bound_x:w){
      exists(bound_x_2:unique_type(s,[mvar:s#0])){
        and(is(bound_x_2,s),
            fun_relation([g@assert(bound_fun:arrow(w,s)){
                            forall(bound_x:s){
                              unique(preimage(w,s,bound_x,bound_fun))}}#0])(bound_x,bound_x_2))}};
    3:preimage(w,
               s,
               [mvar:s#0],
               [g@assert(bound_fun:arrow(w,s)){
                  forall(bound_x:s){
                    unique(preimage(w,s,bound_x,bound_fun))}}#0]);
    4:apply_some(fun_relation([g@assert(bound_fun:arrow(w,s)){
                                 forall(bound_x:s){
                                   unique(preimage(w,s,bound_x,bound_fun))}}#0]),
                 unique_type(s,[mvar:s#0]));
    5:lambda(bound_fun:arrow(w,s)){
      apply_some(fun_relation(bound_fun),
                 unique_type(s,[mvar:s#0]))}([g@arrow(w,s)#0]);
    6:preimage(w,
               s,
               [mvar:s#0],
               [g@arrow(w,s)#0]);
    7:apply_some(fun_relation([g@arrow(w,s)#0]),
                 unique_type(s,[mvar:s#0]));} **/

sugar(type_of(intern_exp(`g)))
/** {
    63;
    pi(bound_x:w){preimage(s,w,bound_x,f)}} **/


sugar_mvar_subst()
/** {
    54;
    {
      [g@assert(bound_fun:arrow(w,[s@type#0])){
         forall(bound_x:[s@type#0]){
           unique(preimage(w,
                           [s@type#0],
                           bound_x,
                           bound_fun))}}#0];
      [g@lambda(bound_s:type){
         assert(bound_fun:arrow(w,bound_s)){
           forall(bound_x:bound_s){
             unique(preimage(w,bound_s,bound_x,bound_fun))}}}([s@type#0])#0];
      [g@injection(w,[s@type#0])#0];
      [g@assert(bound_fun:arrow(w,s)){
         forall(bound_x:s){
           unique(preimage(w,s,bound_x,bound_fun))}}#0];
      [g@assert(bound_fun:arrow([w@type#1],[s@type#0])){
         forall(bound_x:[s@type#0]){
           unique(preimage([w@type#1],
                           [s@type#0],
                           bound_x,
                           bound_fun))}}#0];
      [g@lambda(bound_s:type){
         assert(bound_fun:arrow([w@type#1],bound_s)){
           forall(bound_x:bound_s){
             unique(preimage([w@type#1],
                             bound_s,
                             bound_x,
                             bound_fun))}}}([s@type#0])#0];
      [g@injection([w@type#1],[s@type#0])#0];
      [g@injection(w,s)#0];
      [g@injection(w,s)#0];
      [g@injection([w@type#1],[s@type#0])#0];
      [g@lambda(bound_s:type){
         assert(bound_fun:arrow([w@type#1],bound_s)){
           forall(bound_x:bound_s){
             unique(preimage([w@type#1],
                             bound_s,
                             bound_x,
                             bound_fun))}}}([s@type#0])#0];
      [g@assert(bound_fun:arrow([w@type#1],[s@type#0])){
         forall(bound_x:[s@type#0]){
           unique(preimage([w@type#1],
                           [s@type#0],
                           bound_x,
                           bound_fun))}}#0];
      [g@assert(bound_fun:arrow(w,s)){
         forall(bound_x:s){
           unique(preimage(w,s,bound_x,bound_fun))}}#0];
      [g@injection(w,[s@type#0])#0];
      [g@lambda(bound_s:type){
         assert(bound_fun:arrow(w,bound_s)){
           forall(bound_x:bound_s){
             unique(preimage(w,bound_s,bound_x,bound_fun))}}}([s@type#0])#0];
      [g@assert(bound_fun:arrow(w,[s@type#0])){
         forall(bound_x:[s@type#0]){
           unique(preimage(w,
                           [s@type#0],
                           bound_x,
                           bound_fun))}}#0];
      [g@pi(bound_x:w){preimage(s,w,bound_x,f)}#0];
      [g@arrow([w@type#1],s)#0];
      [g@arrow([w@type#1],s)#0];
      [g@arrow(w,[s@type#0])#0];
      [g@arrow([w@type#1],[s@type#0])#0];
      [g@arrow(w,s)#0];
      [f@bijection([s@type#0],[w@type#1])#0];
      [w@type#1];
      [s@type#0]}} **/

finish_event();
/** {
    in event bijections_invert;
    1.show_decl(s:type);
    2.show_decl(w:type);
    3.show_assume(inhabited(bijection(s,w)));
    4.push_goal(inhabited(bijection(w,s)));
    5.using_decl(f:bijection(s,w));
    6.define(g,
             lambda(bound_x:w){
               the(preimage(s,w,bound_x,f))});
    completed analyzing s;
    completed analyzing w;
    completed analyzing inhabited(bijection(w,s));
    goal failed,looping step of classifying g;
    7.classifying g;
    8.analyzing s;
    goal not achieved;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/


int_exp(max_total[0])
/** {62;6090} **/

theorem empty_uniqueness (c:type2) {
  unique(assert(phi:c=>bool){not(inhabited(assert(s:c){phi(s)}))})}{
  show(x1:assert(phi:c=>bool){not(inhabited(assert(s:c){phi(s)}))},
       x2:assert(phi:c=>bool){not(inhabited(assert(s:c){phi(s)}))}){
    x1=x2}};
/**  **/

why_true(false)
/** {
    63;
    {
      truth_of(false);
      follows by not_contradiction from;
      1:truth_of(inhabited(assert(bound_x:c){
                             [mvar:arrow(c,bool)#0](bound_x)}));
      2:truth_of(not(inhabited(assert(bound_x:c){
                                 [mvar:arrow(c,bool)#0](bound_x)})))}} **/

why(1)
/** {
    64;
    {
      truth_of(inhabited(assert(bound_x:c){
                           [mvar:arrow(c,bool)#0](bound_x)}));
      follows by habitation_witness from;
      1:truth_of(is([mvar:c#0],
                    assert(bound_x:c){
                      [mvar:arrow(c,bool)#0](bound_x)}));
      2:truth_of(conservative([mvar:c#0],true))}} **/


why(1)
/** {
    65;
    {
      truth_of(is([mvar:c#0],
                  assert(bound_x:c){
                    [mvar:arrow(c,bool)#0](bound_x)}));
      follows by assert_safety3 from;
      1:safety_of(assert(bound_x:c){
                    [mvar:arrow(c,bool)#0](bound_x)});
      2:truth_of([mvar:arrow(c,bool)#0]([mvar:c#0]))}} **/

why(2)
/** {
    66;
    {
      truth_of([mvar:arrow(c,bool)#0]([mvar:c#0]));
      follows by safety_assert2 from;
      1:safety_of(assert(bound_x:c){
                    [mvar:arrow(c,bool)#0](bound_x)})}} **/


theorem test_injectivity (s:set, w:set, f:injection(s,w), x_2:s, x_3:s, f(x_2)=f(x_3)){
  x_2=x_3}{
  with(focus(f(x_2)), focus(x_3), focus(x_2))};

theorem Schroeder_Bernstein (s:set, w:set, inhabited(injection(s,w))&&inhabited(injection(w,s))) {
  inhabited(bijection(s,w))}{
  with(f:injection(s,w),
       g:injection(w,s),
       use_f =μ lambda(x:s){
         not(exists(y:preimage(w,s,x,g)){
               not(exists(z:preimage(s,w,y,f)){
                     use_f(z)})})}){
    
    show(x:s){
      use_f(x) = use_f(g(f(x)))}{
      with(assert_type_from_use_f = 
           assert(yyy:preimage(w,s,g(f(x)),g)){
             not(exists(xxx:preimage(s,w,yyy,f)){
                   use_f(xxx)})}){
        
        //it would be helpful for user to indicate intention about habitation and system to complain
        //here we need refutation to see type habitation and that isn't tried in adjust_formula because we don't have a way to tell it our expectation
        show_case(not(inhabited(assert_type_from_use_f))){
          with(assume_not_goal, focus(x), focus(f(x)), focus(g(f(x))))
          };
        
        //it would be helpful for user to indicate intention about habitation and system to complain
        with(assume_not_goal, //needed here to see next type inhabited. NOTE: no way to specify this analysis on the way out/popping
             yy:assert_type_from_use_f){
          show{yy=f(x)}{with(focus(yy), focus(x), focus(f(x)), focus(g(f(x))),)}; //any such yy is f(x) given injectivity of g
          }}};
    
    with(h = lambda(x:s){if(use_f(x),f(x),the(y:w){g(y)=x})}){
      show(){is(h,injection(s,w))}{
        show(y:w,
             x_2:preimage(s,w,y,h),
             x_3:preimage(s,w,y,h)){
          x_2 = x_3
          }{
          show(use_f(x_2)){use_f(x_3)}{with(focus(x_2), assume_not_goal)};
          show(use_f(x_3)){use_f(x_2)}{with(focus(x_3), assume_not_goal)};
          with(assume_not_goal,focus(x_2), focus(x_3))}};

      show(){is(h,surjection(s,w))}{
        show(y:w){exists(x:s){h(x)=y}}{
          show_case(not(inhabited(preimage(s,w,y,f)))){
            with(focus(y), focus(g(y))){
              show{not(use_f(g(y)))}{
                with(assume_not_goal)};}};
          show_case(use_f(g(y))){
            //this case unfinished
            with(pre = the(preimage(s,w,y,f))){
              show{is(y,preimage(w,s,g(y),g))};
              show(use_f(pre)){
                with(focus(g(y)),focus(y), focus(pre), assume_not_goal)};
              with(focus(g(y)),
                   focus(pre))}}}}}}};


//WORKING PROOF OF INJECTION SUPERSEDED ABOVE
// injection works but needs exploration. Also still want to try the() and taxonomic
theorem Schroeder_Bernstein (s:set, w:set, inhabited(injection(s,w))&&inhabited(injection(w,s))) {
  inhabited(bijection(s,w))}{
  with(f:injection(s,w),
       g:injection(w,s),
       use_f =μ lambda(x:s){
         not(exists(y:preimage(w,s,x,g)){
               not(exists(z:preimage(s,w,y,f)){
                     use_f(z)})})}){
    with(h = lambda(x:s){if(use_f(x),f(x),the(y:w){g(y)=x})}){
      show(){is(h,injection(s,w))}{
        show(x:s){use_f(x) |=> f(x)=h(x)};
        show(x:s){not(use_f(x)) |=> the(y:w){g(y)=x}=h(x)};
        show(y:w){unique(preimage(s,w,y,f))};
        show(x:s){unique(preimage(w,s,x,g))};
        
        //show(x:s){is(preimage(w,s,x,g),w)}; need guidance on this
        
        show(x:s, //apply fixed point of use_f
             not(use_f(x)),
             y:preimage(w,s,x,g),
             xx:preimage(s,w,y,f)){
          not(use_f(xx))}{
          with(yy:assert(yyy:preimage(w,s,x,g)){
                 not(exists(xxx:preimage(s,w,yyy,f)){use_f(xxx)})}){
            show{yy=y}{with(focus(y), focus(yy))};}};
        
        //explore why this doesn't eliminate the body in show_case_contradictory
        //show(x:s,
               //   not(use_f(x))){
          //forall(y:preimage(w,s,x,g)){
            //  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
        show(x_1:w,
             x_2:preimage(s,w,x_1,h),
             x_3:preimage(s,w,x_1,h)){
          x_2 = x_3
          }{
          show_case_contradictory(use_f(x_2) && not(use_f(x_3))){
            with(focus(x_3), focus(x_1), focus(x_2)){
              //show{forall(y:preimage(w,s,x_3,g)){
                  //  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
              show{forall(y:preimage(w,s,x_3,g)){
                  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
              }};
          show_case_contradictory(use_f(x_3) && not(use_f(x_2))){
            with(focus(x_3), focus(x_1), focus(x_2))};
          with(assume_not_goal,focus(x_2), focus(x_3)){
            show_case(use_f(x_3))}}};
      show(){is(h,surjection(s,w))}{
        show(x1:w){exists(x2:s){h(x2)=x1}}{
          show_case(use_f(g(x1))){
            with(focus(g(x1)),
                 z:assert(x2:s){f(x2)=x1},
                 focus(z))}}}}}};


//trying ontic approach
theorem Schroeder_Bernstein (s:set, w:set, inhabited(injection(s,w))&&inhabited(injection(w,s))) {
  inhabited(bijection(s,w))}{
  
  with(f:injection(s,w),
       g:injection(w,s),
       covered_by_g =μ lambda(y:w){
         not(inhabited(preimage(s,w,y,f))) 
         || exists(yy:w){covered_by_g(yy) && y=f(g(yy))}}){
    show(x:s,covered_by_g(f(x))){ //the() safety for defining h()
      inhabited(preimage(w,s,x,g))}{
      with(focus(f(x)), //needed to avoid existence supposition for y:
           y:assert(yy:w){covered_by_g(yy) && f(x)=f(g(yy))}){
        show{is(y,preimage(w,s,x,g))}{
          show{x=g(y)}{with(focus(g(y)))};};}};
    with(uses_g = lambda(x:s){exists(y:preimage(w,s,x,g)){covered_by_g(y)}},
         h = lambda(x:s){if(uses_g(x),
                            the(preimage(w,s,x,g)),
                            f(x))}){
      show(){is(h,injection(s,w))}{
        show(y:w,
             x_2:preimage(s,w,y,h),
             x_3:preimage(s,w,y,h)){
          x_2=x_3}{
          show_case(uses_g(x_2)){
            show{unique(preimage(w,s,x_2,g))}{with(focus(x_2))};
            show{h(x_2)=the(preimage(w,s,x_2,g))};
            show{h(x_2)=y};
            show{covered_by_g(y)};
            show_case(not(uses_g(x_3))){
              
              };
            with(focus(x_2),focus(x_3))
            };
          show_case(not(uses_g(x_2)));}};}}};

//not used below here, obsolete
define inverse(s:set,w:set,f:bijection(s,w)){
  assert(g:bijection(w,s)){
    forall(x:w){f(g(x))=x} &&
    forall(y:s){g(f(y))=y}}};

theorem inverses_exist (s:set, w:set, f:bijection(s,w)){
  inhabited(inverse(s,w,f))}{
  let(g = lambda(x:w){the(y:s){f(y)=x}}){
    lemma{show(is(g,bijection(w,s)))}}
  };
