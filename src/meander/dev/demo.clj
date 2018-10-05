(ns meander.dev.demo
  (:require
   [clojure.set :as set]
   [clojure.spec.alpha :as s]
   [clojure.string :as string]
   [clojure.java.io :as jio]
   [meander.dev.strategy :as r]
   [meander.dev.match :as r.match]
   [meander.dev.search :as r.search]
   [meander.dev.substitute :as r.substitute]
   [meander.dev.syntax :as r.syntax]))


;; ---------------------------------------------------------------------
;; Clojure AST

(declare clj=>ast)

(defn const=>ast [env]
  (fn [x]
    (let [type (cond
                 (char? x)
                 :char

                 (boolean? x)
                 :bool

                 (keyword? x)
                 :keyword

                 (nil? x)
                 :nil

                 (number? x)
                 :number

                 (map? x)
                 :map

                 (instance? java.util.regex.Pattern x)
                 :regex

                 (set? x)
                 :set

                 (seq? x)
                 :seq

                 (string? x)
                 :string

                 (symbol? x)
                 :symbol

                 (vector? x)
                 :vector

                 :else
                 :unkown)]
      {:op :const
       :form x
       :literal? true
       :type type
       :val x
       :children []})))


(defn def=>ast [env]
  (r/matcht
   ((def (? symbol? ?name) ?doc ?init) :as ?form)
   (let [init (clj=>ast env ?init)
         var (ns-resolve *ns* ?name)
         meta (when var (meta var))
         children (cond-> []
                    (some? meta)
                    (conj :meta)

                    (some? init)
                    (conj :init))]
     {:op :def
      :env env
      :form ?form
      :name ?name
      :var var
      :meta meta
      :init init
      :doc ?doc
      :children children})

   ((def (? symbol? ?name) ?init) :as ?form)
   (let [init (clj=>ast env ?init)
         var (ns-resolve *ns* ?name)
         meta (when var (meta var))
         doc (:doc meta)
         children (cond-> []
                    (some? meta)
                    (conj :meta)

                    (some? init)
                    (conj :init))]
     {:op :def
      :env env
      :form ?form
      :name ?name
      :var var
      :meta meta
      :init init
      :doc doc
      :children children})

   ((def (? symbol? ?name)) :as ?form)
   (let [var (ns-resolve *ns* ?name)
         meta (when var (meta var))
         doc (:doc meta)
         children (cond-> []
                    (some? meta)
                    (conj :meta))]
     {:op :def
      :env env
      :form ?form
      :name ?name
      :var var
      :meta meta
      :init nil
      :doc doc
      :children children})))


(defn do=>ast [env]
  (r/matcht
   (do)
   {:op :do
    :env env
    :form '(do)
    :statments []
    :ret nil
    :children [:statements :ret]}

   ((do . !statements ... . ?ret) :as ?form)
   (let [statements (mapv (clj=>ast env) !statements)
         ret (clj=>ast env ?ret)]
     {:op :do
      :env env
      :form ?form
      :statments statements
      :ret ret
      :children [:statements :ret]})))


(defn invoke=>ast [env]
  (r/matcht
   ((?f . !args ...) :as ?form)
   (r.match/match (macroexpand ?form)
     ~?form
     (let [fn (clj=>ast env ?f)
           args (mapv (clj=>ast env) !args)]
       {:op :invoke
        :env env
        :form ?form
        :fn fn
        :args args
        :meta (meta ?form)
        :children [:fn :args]})

     ?mform
     (assoc (clj=>ast env ?mform) :raw-form ?form))))


(defn quote=>ast [env]
  (r/matcht
   ('quote ?x)
   {:op :quote
    :env nil
    :expr ((const=>ast env) ?x)
    :form ?x
    :literal? true
    :chidren [:expr]}))


(defn new=>ast [env]
  (r/matcht
   ((new (? symbol? ?class) . !args ...) :as ?form)
   (let [args (mapv (clj=>ast env) !args)]
     {:op :new
      :env env
      :form ?form
      :class ?class
      :args args
      :children [:args]})))


(defn if=>ast [env]
  (r/matcht
   ((if ?test ?then ?else) :as ?form)
   (let [test (clj=>ast env ?test)
         then (clj=>ast env ?then)
         else (clj=>ast env ?else)]
     {:op :if
      :env env
      :form ?form
      :test test
      :then then
      :else else
      :children [:test :then :else]})

   ((if ?test ?then) :as ?form)
   (let [test (clj=>ast env ?test)
         then (clj=>ast env ?then)]
     {:op :if
      :env env
      :form ?form
      :test test
      :then then
      :else nil
      :children [:test :then]})))


(defn field-symbol? [x]
  (and (simple-symbol? x)
       (. (name x) startsWith "-")))


(defn host-field=>ast [env]
  (r/matcht
   (('. ?target ((? field-symbol?) :as ?field))
    :as ?form)
   (let [target (clj=>ast env ?target)
         field (symbol (subs (name ?field) 1))]
     {:op :host-field
      :env env
      :form ?form
      :target target
      :field field
      :children [:target]})))


(defn host-call=>ast [env]
  (r/matcht
   (('. ?target ((and (? simple-symbol?)
                      (? (complement field-symbol?)))
                 :as ?method) . !args ...)
    :as ?form)
   (let [target (clj=>ast env ?target)
         args (mapv (clj=>ast env) !args)]
     {:op :host-call
      :env env
      :form ?form
      :target target
      :method ?method
      :args args
      :children [:target :args]})))


(defn maybe-class=>ast [env]
  (r/pipe
   (r/pred
    (fn [t]
      (and (symbol? t)
           (Character/isUpperCase (. (name t) charAt 0)))))
   (fn [form]
     {:op :maybe-class
      :env env
      :form form
      :class form})))

(defn let-binding-node
  [env sym init]
  {:op :binding
   :env env
   :form sym
   :name sym
   :local :let
   :init init
   :children [:init]})

(defn clj=>ast*
  [env forms]
  (second
   (reduce
    (fn [[env* nodes] form]
      (let [node (clj=>ast env* form)]
        [(:env node env*) (conj nodes node)]))
    [env []]
    forms)))


(defn let=>ast [env]
  (r/matcht
   ((let* [(_ _ :as !bindings) ...] . !exprs ...) :as ?form)
   (loop [!bindings !bindings
          binding-nodes []
          env* env]
     (if-some [[[sym init] & !bindings*] (seq !bindings)]
       (let [binding-node (let-binding-node env* sym (clj=>ast env* init))]
         (recur !bindings*
                (conj binding-nodes binding-node)
                (update env* :locals (fnil conj #{}) sym)))
       {:op :let
        :env env
        :form ?form
        :bindings binding-nodes
        :body (clj=>ast* env* !exprs)
        :children [:bindings :body]}))))

(defn binding=>ast
  [env]
  (fn [t]
    (if (contains? (:locals env) t)
      {:op :local
       :env env
       :form t
       :name t
       :children []}
      r/*fail*)))

(defn clj=>ast
  ([env]
   (r/choice
    (do=>ast env)
    (def=>ast env)
    (new=>ast env)
    (if=>ast env)
    (quote=>ast env)
    (host-call=>ast env)
    (host-field=>ast env)
    (let=>ast env)
    (invoke=>ast env)
    (maybe-class=>ast env)
    (binding=>ast env)
    (const=>ast env)))
  ([env clj-form]
   ((clj=>ast env) clj-form)))


;; ---------------------------------------------------------------------
;; Clojure AST => Ruby AS


(declare clj-ast=>rb-ast)


(def clj-def-ast=>rb-ast
  (r/matcht
   {:op :def
    :name ?name
    :init ?init}
   (let [const-name (gensym "C__")]
     {:op :ruby/begin
      :statements [{:op :ruby/casgn
                    :parent nil
                    :name const-name
                    :init (clj-ast=>rb-ast ?init)
                    :children [:init]}
                   {:op :ruby/def
                    :name (name ?name)
                    :params []
                    :body [{:op :ruby/const
                            :parent nil
                            :name const-name}]
                    :children [:params :body]}]
      :children [:statements]})))

(def clj-const-ast=>rb-ast
  (r/matcht
   {:op :const
    :type ?type
    :val ?val}
   {:op (case ?type
          :number
          (if (integer? ?val)
            :ruby/int
            :ruby/float))
    :val ?val}))


(def clj-if-ast=>rb-ast
  (r/matcht
   {:op :if
    :test ?test
    :then ?then
    :else ?else}
   {:op :ruby/if
    :test (clj-ast=>rb-ast ?test)
    :then (clj-ast=>rb-ast ?then)
    :else (clj-ast=>rb-ast ?else)}))

(def clj-let-ast=>rb-ast
  (r/matcht
   {:op :let
    :bindings ?bindings
    :body ?body}
   {:op :ruby/begin
    :statements (mapv clj-ast=>rb-ast (concat ?bindings ?body))}))


(def clj-binding-ast=>rb-ast
  (r/matcht
   {:op :binding
    :form ?form
    :name ?name
    :init ?init}
   {:op :ruby/lvasgn
    :name ?name
    :init (clj-ast=>rb-ast ?init)}))

(def clj-host-call-ast=>rb-ast
  (r/matcht
   {:op :host-call
    :method ?method
    :target ?target
    :args ?args}
   {:op :ruby/send
    :method (str ?method)
    :target (clj-ast=>rb-ast ?target)
    :args (mapv clj-ast=>rb-ast ?args)}))

(def clj-local-ast=>rb-ast
  (r/matcht
   {:op :local
    :name ?name}
   {:op :ruby/lvar
    :name ?name}))



(def
  ^{:arglists '([clj-ast])}
  clj-ast=>rb-ast
  (r/choice
   clj-def-ast=>rb-ast
   clj-const-ast=>rb-ast
   clj-if-ast=>rb-ast
   clj-let-ast=>rb-ast
   clj-binding-ast=>rb-ast
   clj-local-ast=>rb-ast
   clj-host-call-ast=>rb-ast))

(declare rb-ast=>string)

(defn indent [s]
  (string/replace s #"(?m:(?=^))" "  "))

(def rb-ast-def=>string
  (r/matcht
   {:op :ruby/def
    :name ?name
    :params ?params
    :body ?body}
   (with-out-str
     (printf "def %s(%s)" ?name "_todo_")
     (println)
     (println
      (indent
       (rb-ast=>string
        {:op :ruby/begin
         :statements ?body})))
     (println "end"))))

(def rb-ast-begin=>string
  (r/matcht
   {:op :ruby/begin
    :statements ?statements}
   (string/join "\n" (map rb-ast=>string ?statements))))

(def rb-ast-const=>string
  (r/matcht
   {:op :ruby/const
    :parent ?parent
    :name ?name}
   (if ?parent
     (str (rb-ast=>string ?parent) "::" ?name)
     ?name)))

(def rb-ast-number=>string
  (r/matcht
   {:op (or :ruby/int :ruby/float)
    :val ?val}
   (str ?val)))

(def rb-ast-lvar=>string
  (r/matcht
   {:op :ruby/lvar
    :name ?name}
   (name ?name)))

(def rb-ast-lvasgn=>string
  (r/matcht
   {:op :ruby/lvasgn
    :name ?name
    :init ?init}
   (format "%s = %s"
           (name ?name)
           (rb-ast=>string ?init))))

(def rb-ast-casgn=>string
  (r/matcht
   {:op :ruby/casgn
    :parent ?parent
    :name ?name
    :init ?init}
   (format "%s = %s"
           (if ?parent
             (str (rb-ast=>string ?parent) "::" ?name)
             ?name)
           (rb-ast=>string ?init))))

(def rb-ast-maybe-class=>string
  (r/matcht
   {:op :maybe-class
    :class ?class}
   (str ?class)))

(def rb-ast-send=>string
  (r/matcht
   {:op :ruby/send
    :method ?method
    :target ?target
    :args ?args}
   (format "(%s).%s(%s)"
           (rb-ast=>string ?target)
           ?method
           (string/join "," (map rb-ast=>string ?args)))))

(def rb-ast-if=>string
  (r/matcht
   {:op :ruby/if
    :test ?test
    :then ?then
    :else ?else}
   (with-out-str
     (print "if ")
     (print "(")
     (print (rb-ast=>string ?test))
     (println ")")
     (indent
      (with-out-str
        (println (rb-ast=>string ?then))))
     (println "else")
     (indent
      (with-out-str
        (println (rb-ast=>string ?else))))
     (println "end"))))


(def rb-ast=>string
  (r/choice
   rb-ast-def=>string
   rb-ast-begin=>string
   rb-ast-const=>string
   rb-ast-casgn=>string
   rb-ast-maybe-class=>string
   rb-ast-number=>string
   rb-ast-send=>string
   rb-ast-if=>string
   rb-ast-lvar=>string
   rb-ast-lvasgn=>string
   identity))


;; ---------------------------------------------------------------------
;; CEK machine


(def
  ^{:arglists '([[c ρ κ]])
    :doc "CEK machine step function. Takes a CEK triple ς and returns
    the subsequent CEK triple ς′. If ς = ς′ the machine is in a halted
    state (or the input was invalid)."}
  cek-step
  (r/matcht
   ;; ⟨x, ρ, κ⟩ --> ⟨v, ρ′, κ⟩ where ρ(x) = (v, ρ′)
   [(? symbol? ?x) ?ρ ?k]
   (if-some [[_ [v ρ*]] (find ?ρ ?x)]
     [v ρ* ?k]
     [?x ?ρ [:error ?x ?k]])

   ;; ⟨(e₀ e₁), ρ, κ⟩ --> ⟨e₀, ρ, ar(e₁, ρ, κ)⟩
   [(?e₀ ?e₁) ?ρ ?k]
   [?e₀ ?ρ [:ar ?e₁ ?ρ ?k]]

   ;; ⟨v, ρ, ar(e, ρ′, κ)⟩ --> ⟨e, ρ′, fn(v, ρ, κ)⟩
   [?v ?ρ [:ar ?e ?ρ* ?k]]
   [?e ?ρ* [:fn ?v ?ρ ?k]]

   ;; ⟨v, ρ, fn((λx.e), ρ′, κ)⟩ -->  ⟨e, ρ′[x → (v, ρ)], κ⟩
   [?v ?ρ [:fn (fn [?x] ?e) ?ρ* ?k]]
   [?e (assoc ?ρ* ?x [?v ?ρ]) ?k]

   ;; Default, no action.
   ?ς
   ?ς))


;; ---------------------------------------------------------------------
;; Form search


(require '[clojure.tools.reader :as read])
(require '[clojure.tools.reader.reader-types :as read.types])


(defn alias-map
  "When passed an (ns ,,,) form attempt to derive a map from ns-alias
  symbol to ns symbol. Returns nil fails if such a map cannot be
  derived."
  [form]
  ;; TODO: (require ,,,)
  (r.match/when-match form
    ;; NOTE: For some reason ns needs to be quoted but I don't know
    ;; why. The macro expansion correctly emits (list 'ns) but if left
    ;; unquoted causes issues. This seems to be a problem when using
    ;; cider and does not seem to be a problem when used at the
    ;; command line REPL.
    ('ns . (_ ... :as ?form))
    (r.match/when-match (s/conform :clojure.core.specs.alpha/ns-form ?form)
      {:clauses ?clauses}
      (into {}
            (mapcat
             (fn [clause]
               (r.match/when-match clause
                 [:require {:body ?body}]
                 (map
                  (fn [x]
                    (r.match/when-match x
                      [:libspec
                       [:lib+opts {:lib ?ns-sym
                                   :options {:as ?ns-alias}}]]
                      [?ns-alias ?ns-sym]))
                  ?body))))
            ?clauses))
    ;; TODO
    #_ (require . !args ...)))


(defn read-forms-from-file
  [^java.io.File file]
  (let [source (.getCanonicalPath file)
        rdr (java.io.FileReader. file)
        pbr (java.io.PushbackReader. rdr)
        pbr (read.types/source-logging-push-back-reader pbr)
        eof (Object.)
        ;; This environment is for seq.
        env1 (volatile! {})
        ;; This environment is for reduce.
        env2 (volatile! {})]
    (reify
      clojure.lang.Seqable
      (seq [this]
        ((fn step []
           (let [form (binding [read/*alias-map* @env1]
                        (read/read {:eof eof} pbr))
                 form (if-some [m (meta form)]
                        (vary-meta form assoc :source source)
                        form)]
             (when-some [m (alias-map form)]
               (vswap! env1 merge m))
             (if (identical? form eof)
               ()
               (lazy-seq (cons form (step))))))))

      clojure.lang.IReduceInit
      (reduce [this f init]
        (loop [acc init]
          (if (reduced? acc)
            acc
            (let [form (binding [read/*alias-map* @env2]
                         (read/read {:eof eof} pbr))
                  form (if-some [m (meta form)]
                         (vary-meta form assoc :file source)
                         form)]
              (when-some [m (alias-map form)]
                (vswap! env2 merge m))
              (if (identical? form eof)
                acc
                (recur (f acc form))))))))))


(defn cljq
  ([query]
   (fn [forms]
     (cljq query forms)))
  ([query forms]
   (let [result-sym (gensym "?res__")
         qvars (map r.syntax/data
                    (r.syntax/variables
                     (r.syntax/parse query)))
         query* (list query :as result-sym)
         s (eval
            `(r/extract
              (fn [t#]
                (try
                  ((r/matcht
                    ~query*
                    [(assoc (meta ~result-sym)
                            :tag :match/pattern
                            :match ~result-sym)
                     ~@(map
                        (fn [qvar]
                          `(assoc (meta ~qvar)
                                  :tag :match/var
                                  :var '~qvar
                                  :match ~qvar)) 
                        qvars)])
                   t#)
                  (catch Exception e#
                    r/*fail*)))))]
     (into #{}
           (comp (mapcat s)
                 (mapcat identity))
           forms))))


(defn cljq-index-key
  "Returns the index key which corresponds to form."
  [form]
  ;; There is a bug(?) in the pattern match compiler which causes the
  ;; patterns in this match to be skipped if any of
  ;;
  ;;   (?pat ':as _)
  ;;   ('and . _ ...)
  ;;   ('? . _ ...)
  ;;
  ;; succeed in the seq? check they compile to.
  (r.match/match form
    (? seq?)
    (r.match/match form
      (?pat ':as _)
      (cljq-index-key ?pat)

      ('and . _ ...)
      :all

      ('? . _ ...)
      :all

      _
      :seq)

    (? vector?)
    :vec

    (? map?)
    :map

    (? set?)
    :set

    (? symbol?)
    :sym

    (? keyword?)
    :key

    _
    :all))


(defn cljq-index-forms
  [forms]
  (let [all-forms (vec (tree-seq
                        (every-pred (complement map-entry?) coll?)
                        seq
                        (vec forms)))]
    (assoc (group-by cljq-index-key all-forms)
           :all all-forms)))


(def cljq-app-state
  (atom {}))


(defn cljq-file-index
  "Returns the current form index for file."
  [^java.io.File file]
  (let [file-name (.getCanonicalPath file)]
    (if-some [[_ [last-known-mod-time index]] (find @cljq-app-state file-name)]
      (let [current-mod-time (.lastModified file)]
        (if (not= last-known-mod-time current-mod-time)
          (let [index* (cljq-index-forms (read-forms-from-file file))]
            (prn {:cljq/event :cljq.index/update
                  :cljq.index/name file-name})
            (swap! cljq-app-state assoc file-name [current-mod-time index*])
            index*)
          index))
      (let [current-mod-time (.lastModified file)
            index* (cljq-index-forms (read-forms-from-file file))]
        (prn {:cljq/event :cljq.index/create
              :cljq.index/name file-name})
        (swap! cljq-app-state assoc file-name [current-mod-time index*])
        index*))))


(defn cljq-file
  "Execute a cljq query against file."
  [q ^java.io.File file]
  (cljq q (get (cljq-file-index file) (cljq-index-key q))))


(defn cljq-dir
  "Execute a cljq query against a directory."
  [q ^java.io.File dir]
  (sequence
   (comp
    (filter
     (fn [^java.io.File f]
       (and (.isFile f)
            (.endsWith (.getName f) ".clj"))))
    (mapcat
     (fn [f]
       (cljq-file q f))))
   (file-seq dir)))


(defn cljq-pattern-match?
  [x]
  (and (map? x)
       (if-some [[_ tag] (find x :tag)]
         (= tag :match/pattern)
         false)))


(defn cljq-var-match?
  [x]
  (and (map? x)
       (if-some [[_ tag] (find x :tag)]
         (= tag :match/var)
         false)))


(defn symbol-like-fn
  ([re]
   (fn [x]
     (and (symbol? x)
          (re-find re (str x))))))


(import '[java.util.regex Pattern])

(defn clj-sr-apply [file results]
  (let [buffer (slurp file)]
    (reduce
     (fn [buffer result]
       (let [replacement-string (clojure.string/trim
                                 (with-out-str (clojure.pprint/pprint (:replacement result))))
             pattern (re-pattern (Pattern/quote (:source result)))
             matcher (re-matcher pattern buffer)]
         (.replaceFirst matcher replacement-string)))
     buffer
     (sort-by :line results))))



(defmacro clj-search-and-replace [file match replacement]
  `(clj-sr-apply (jio/file ~file)
                 (sequence
                  (comp (filter (comp #{:match/pattern} :tag))
                        (map
                         (r/rewritet
                          {:line ~'?line
                           :source ~'?source
                           :tag :match/pattern
                           :match ~match}
                          ;; =>
                          {:line ~'?line
                           :source ~'?source
                           :replacement ~replacement})))
                  (cljq-dir '~match (jio/file ~file)))))


#_
(let [file (jio/file "/Users/noprompt/git/healthfinch/hf-crede-rules-clj/src/crede/message/pre_visit_message.clj")]
  (spit file
        (clj-search-and-replace
         file
         (ruby/call-ruby
          (hf.document/make-handler
           {:format "ascii_columns"
            :options ?options})
          :call
          (zweikopf.core/rubyize ?context))
         ((hf.document/make-handler
           {:format :ascii-row
            :row ?options})
          ?context))))



;; Body
;;
;; And: b₁, b₂
;; Choose: b₁;b₂
;; Unify: x₁ = x₂
;; Call: call(t)
;;   foo(X), bar(Y).
;;   =>
;;   call(foo(X)), call(bar(Y)).
;; Bind: x ← t
;;   foo(X, Y) = foo(bar, baz).
;;   =>
;;   T1 ← foo(X, Y),
;;   T2 ← bar(),
;;   T3 ← baz(),
;;   T4 ← foo(T2, T3),
;;   T1 = T4.
;; Is: x is e
;;   X = 1.
;;   =>
;;   T1 is 1,
;;   X = T1,
;; RelationalBody: x₁ ⊛ x₂
;;   X > 7.
;;   T1 is 7,
;;   X > T1.
;; True: true
;; Fail: fail
;; ArithExp
;; ArithOp
;; RelationalOp
;;
;; n ∈ ℕ
;; db ∈ ClauseDb = (Name × ℕ) ↦ Clause
;; ρ ∈ Env = Variable ↦ Placeholder
;; κ ∈ Kont = andK(Body) + restoreK(Env)
;; v ∈ Value = IntValue + TermValue + Placeholder
;; iv ∈ IntValue = intValue(ℤ)
;; tv ∈ TermValue = termValue(Name, Value→)
;; pl ∈ Placeholder = placeholder(ℕ)
;; eq ∈ EquivClasses = Placeholder ↦ Value
;; ch ∈ Choice = Body × Env × EquivClasses × Kont→
;; ς ∈ State =  Body × Env × EquivClasses × Kont→ × Choice→


(defn mpl-lookup [v eq]
  (if-some [[_ pl] (find eq v)]
    (mpl-lookup pl eq)
    v))


(defn mpl-add-relation [pl v eq]
  (let [v* (mpl-lookup v eq)]
    (if (= pl v*)
      eq
      (assoc eq pl v*))))


(declare mpl-unify-vals)


(defn mpl-unify-multi-vals [pairs eq]
  (r.match/match pairs
    [[?v1 ?v2] . !pairs ...]
    (if (some? (mpl-unify-vals ?v1 ?v2 eq))
      (mpl-unify-multi-vals !pairs eq))

    _
    eq))


#_
(mpl-unify-vals '(termValue foo [(placeholder 1)])
                '(termValue foo [(placeholder 2)])
                {})

(defn mpl-unify-vals [v1 v2 eq]
  (let [v3 (mpl-lookup v1 eq)
        v4 (mpl-lookup v2 eq)]
    (r.match/match [v3 v4]
      [(placeholder _) _]
      (mpl-add-relation v3 v4 eq)

      [(not (placeholder _)) (placeholder _)]
      (mpl-add-relation v4 v3 eq)

      [(intValue ?i) (intValue ?i)]
      eq

      (and [(termValue ?name [!vs5 ...]) (termValue ?name [!vs6 ...])]
           (? (fn [_]
                (= (count !vs5)
                   (count !vs6)))))
      (mpl-unify-multi-vals (map vector !vs5 !vs6) eq)

      _
      nil)))

