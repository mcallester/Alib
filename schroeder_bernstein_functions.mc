
restart_event(`schroeder_bernstein_functions);

declare_package(`schroeder_bernstein_functions);

theorem emptyset_exists(){
  exists(s:set){not(inhabited(s))}}{
  let(s:set,
      empty=assert(x:s){not(x=x)}){
    suppose_not{let(x:empty)}}};

define injection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      unique(assert(x:s){y = f(x)})}
    }};

define surjection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      exists(x:s){f(x)=y}}}};

define bijection(s:set,w:set){
  assert(f:s=>w){
    is(f,injection(s,w)) && is(f,surjection(s,w))}};

theorem bijections_invert (s:set, w:set) {implies(inhabited(bijection(s,w)), inhabited(bijection(w,s)))} {
  let(f:bijection(s,w)){
    let(g = lambda(x:w){the(y:s){f(y)=x}}){
      show(is(g,surjection(w,s)))}}};

theorem empty_uniqueness (c:class) {
  unique(assert(phi:c=>bool){not(inhabited(assert(s:c){phi(s)}))})};

theorem Schroeder_Bernstein (s:set, w:set) {
  implies(inhabited(surjection(s,w))&&inhabited(injection(w,s)),
          inhabited(bijection(s,w)))}{
  suppose(inhabited(surjection(s,w))&&inhabited(injection(w,s))){
    let(f:injection(s,w),
        g:injection(w,s),
        use_f =μ lambda(x:s){
          not(exists(y:w){
                g(y)=x
                && not(exists(z:s){
                         f(z)=y && use_f(z)})})}){
      let(h = lambda(x:s){if(use_f(x),f(x),the(y:w){g(y)=x})}){
        show(is(h,injection(s,w)));
        show(is(h,surjection(s,w))){
          lemma{
            let(x1:w){
              show(exists(x2:s){h(x2)=x1}){
                /* let(z:assert(z:s){f(z)=x1 && use_f(z)}) */
                suppose(use_f(g(x1))){
                  consider(g(x1),assert(x2:s){f(x2)=x1})}
                /* { */
                  /*   suppose(use_f(g(x1))){ */
                    /*     show(exists(z:s){f(z)=x1 && use_f(z)})} */
                  /*   } */
              }
              }}}}}}};


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
