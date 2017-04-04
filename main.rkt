#lang racket/base

(require racket/match
         racket/string
         racket/system
         math/statistics
         racket/cmdline
         plot)

(struct test-dir (name make clean) #:transparent)

(define targets
  '(math-flonum
    new-metrics
    old-metrics)
  #;'(acquire
    dungeon
    forth
    fsm
    math-flonum
    new-metrics
    old-metrics
    parser
    schml-flatten-values
    schml-interp-casts-help
    schml-specify-rep))

(define verbose-flag? #f)
(define plot-flag? #f)
(define single-target? #f)

(define-values (control-bin test-bin)
  (command-line
   #:program "tr-performance"
   #:once-each
   [("-v" "--verbose") "Build with verbose messages"
                       (set! verbose-flag? #t)]
   [("-p" "--plot") "Plot results"
                    (set! plot-flag? #t)]
   #:multi
   [("-t" "--target") target
                      "Only build a single target"
                      (set! single-target? (string->symbol target))]
   #:args (control test) ; expect one command-line argument: <filename>
   ; return the argument as a filename to compile
   (values control test)))

(unless (file-exists? (build-path control-bin "raco"))
  (error 'tr-performance
         "provided control bin directory did not contain 'raco': ~a"
         control-bin))

(unless (file-exists? (build-path test-bin "raco"))
  (error 'tr-performance
         "provided test bin directory did not contain 'raco': ~a"
         test-bin))

(when single-target?
  (unless (memq single-target? targets)
    (error 'tr-performance
           "'~a not found in list of valid targets: '~a"
           single-target?
           targets)))

(define raco-control (string-append control-bin "/raco"))
(define raco-test (string-append test-bin "/raco"))

(define (round2digit n)
  (/ (round (* n 100.0)) 100.0))

;; time the build of dir/main.rkt
(define (time-single-build dir raco)
  (match-define (list inp outp pid errp cmd)
    (process (format "/usr/bin/time -p ~a make ~a/main.rkt" raco dir)))

  (close-output-port outp)
  (define result (string-split (read-line errp)))
  (close-input-port errp)
  (close-input-port inp)
  (cmd 'kill)
  (unless (system (format "rm -fr ~a/compiled" dir))
    (error 'tr-performance "failed to remove compiled dir for ~a" dir))
  (match result
    [(list "real" time-str) (string->number time-str)]
    [_ (error 'tr-performance "failed to time build for ~a, got ~a" dir result)]))

;; build and time 'dir' several times, calculate mean/stddev
(define (time-dir dir raco)
  (printf "building ~a" dir)
  (flush-output)
  (define iters 10)
  (define times (for/list ([_ (in-range iters)])
                  (begin0 (time-single-build dir raco)
                          (printf ".")
                          (flush-output))))
  (printf "\n")
  (define m (round2digit (mean times)))
  (define s (round2digit (stddev times)))
  (when verbose-flag?
    (printf "~a make ~a:\n  times ~a\n  mean ~a\n  stddev ~a\n"
            raco dir  times m s))
  (printf "done with ~a\n" dir)
  m)

(define results '())

(cond
  [single-target?
   (define control-mean (time-dir single-target? raco-control))
   (define test-mean (time-dir single-target? raco-test))
   (set! results (cons (list single-target? control-mean test-mean)
                       results))]
  [else (for ([t (in-list targets)])
          (define control-mean (time-dir t raco-control))
          (define test-mean (time-dir t raco-test))
          (set! results (cons (list t control-mean test-mean)
                              results)))])

(printf "\nresults:\n")
;; print out results
(for ([r (in-list results)])
  (match r
    [(list name control test)
     (define Δ (* 100 (/ (- test control) control)))
     (printf "~a: ~a% ~a (~as to ~as)\n"
             name
             (round2digit (abs Δ))
             (if (positive? Δ) 'slower 'faster)
             control
             test)]))

(when plot-flag?
  (let-values
      ([(controls tests)
        (for/lists (_1 _2) ([r (in-list results)])
          (match r
            [(list name control test)
             (values (list name 100)
                     (list name (+ 100 (* 100 (/ (- test control) control)))))]))])
    (void (plot (list (discrete-histogram
                       controls
                       #:skip 2.5 #:x-min 0
                       #:label "Control")
                      (discrete-histogram
                       tests
                       #:skip 2.5 #:x-min 1
                       #:label "Test" #:color 2 #:line-color 2))
                #:x-label "lib" #:y-label "Control-normalized Build Time %"
                #:out-file "result-plot.png"))))
