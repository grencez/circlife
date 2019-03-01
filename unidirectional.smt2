
(set-logic UFLIA)

(declare-fun planet (Int Int) Int)

;; The population size + its potential.
(declare-const PlanetSize Int)
(assert (> PlanetSize 0))

;; The step where the initial configuration is repeated.
(declare-const Timespan Int)
(assert (> Timespan 0))

(define-fun valid_time       ((t Int)) Bool  (and (>= t 0) (<= t Timespan)))
(define-fun valid_event_time ((t Int)) Bool  (and (>  t 0) (<= t Timespan)))
(define-fun valid_cell_index ((i Int)) Bool  (and (>= i 0) (< i PlanetSize)))


;; Dead cells have negative values.
(define-fun alive ((t Int) (i Int)) Bool
  (>= (planet t i) 0))

(assert
  (forall ((t Int) (i Int))
    (=> (and (valid_time t) (valid_cell_index i)
             (not (alive t i)))
        (= (planet t i) -1))))


(declare-const Synchrony Bool)

(assert Synchrony)
;(assert (not Synchrony))

(declare-const SomeCellIndex Int)
(declare-const SomeEventTime Int)


(declare-const InductionBasisTime1 Bool)
(declare-const InductionBasisTime2 Bool)
(declare-const InductionBasisTime3 Bool)
(declare-const InductionBasisTime4 Bool)
(declare-const InductionBasisTime5 Bool)
(assert (= InductionBasisTime1 (<= SomeEventTime 1)))
(assert (= InductionBasisTime2 (<= SomeEventTime 2)))
(assert (= InductionBasisTime3 (<= SomeEventTime 3)))
(assert (= InductionBasisTime4 (<= SomeEventTime 4)))
(assert (= InductionBasisTime5 (<= SomeEventTime 5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Boundary Conditions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Values wrap around.
(assert
  (forall ((t Int))
    (=> (valid_time t)
        (and
          (= (planet t -1)
             (planet t (- PlanetSize 1)))
          (= (planet t PlanetSize)
             (planet t 0))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Halp.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun spawn_event ((t Int) (i Int)) Bool
  (and (not (alive (- t 1) i))
       (alive t i)))

(define-fun death_event ((t Int) (i Int)) Bool
  (and (alive (- t 1) i)
       (not (alive t i))))

(define-fun some_event ((t Int) (i Int)) Bool
  (not (= (alive (- t 1) i)
          (alive t i))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; How cells change as time progresses.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Adjacent cells cannot be dead if life is sustained.
(assert
  (forall ((t Int) (i Int))
    (=> (and (valid_time t)
             (valid_cell_index i))
        (or (alive t i)
            (alive t (+ i 1))))))

;; Unless there is a spawn or death, a cell's genome remains constant.
(assert
  (forall ((t Int) (i Int))
    (=> (and (valid_event_time t)
             (valid_cell_index i)
             (not (some_event t i)))
        (= (planet t i)
           (planet (- t 1) i)))))

;; Force something to spawn or die.
(assert
  (forall ((t Int))
    (=> (valid_event_time t)
        (exists ((i Int))
          (and (valid_cell_index i)
               (some_event t i))))))

(assert
  (=> (not Synchrony)
      (forall ((t Int) (i Int) (j Int))
        (=> (and (valid_event_time t)
                 (valid_cell_index i)
                 (valid_cell_index j)
                 (not (= i j)))
            (or (not (some_event t i))
                (not (some_event t j)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Spawning Relation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Whether a cell with the middle given genome can result from
;; cells with the given left and right genomes spawning.
(declare-fun spawnable (Int Int Int) Bool)

;; Restricted to natural numbers.
(assert
  (forall ((p Int) (c Int) (q Int))
    (=> (spawnable p c q)
        (and (>= p 0) (>= c 0) (>= q 0)))))

;;; Whether a cell can result from cells with the given genomes spawning.
;(declare-fun compatible (Int Int) Bool)
(define-fun compatible ((p Int) (q Int)) Bool
  (exists ((c Int))
    (spawnable p c q)))

;; Incompatible with grandparents.
(assert
  (forall ((g Int) (p Int) (c Int)  (q Int) (h Int))
    (=> (and (spawnable g p h)
             (spawnable p c q))
        (and (not (compatible g c))
             (not (compatible c h))))))

;; This is how spawning works.
(assert
  (forall ((t Int) (i Int))
    (=> (and (valid_event_time t)
             (valid_cell_index i)
             (spawn_event t i))
        (spawnable (planet (- t 1) (- i 1))
                   (planet t i)
                   (planet (- t 1) (+ i 1))))))

;; Avoid flapping.
(assert
  (forall ((t Int) (i Int))
    (=> (and (valid_event_time t)
             (valid_cell_index i)
             (death_event t i))
        (not (spawnable (planet t (- i 1))
                        (planet (- t 1) i)
                        (planet t (+ i 1)))))))

(check-sat)



(define-fun Pred_SustainableDeathAddsCompatibility ((t Int) (i Int)) Bool
  (=> (and (valid_event_time t)
           (valid_cell_index i)
           (death_event t i))
      (compatible (planet t (- i 1))
                  (planet t (+ i 1)))))

(define-fun Pred_SustainableDeath ((t0 Int) (t1 Int) (i Int)) Bool
  (=> (and (valid_event_time t1)
           (> t1 t0)
           (spawn_event t1 i))
      (Pred_SustainableDeathAddsCompatibility t0 i)))

(declare-const Lemma_SustainableDeath Bool)
(assert (= Lemma_SustainableDeath
           (Pred_SustainableDeath 1 SomeEventTime SomeCellIndex)))
(check-sat-assuming ((not Lemma_SustainableDeath)
                     InductionBasisTime5))


;; We proved this in a  different file, so just assert it here.
(assert (forall ((t Int) (i Int))
          (Pred_SustainableDeathAddsCompatibility t i)))



;(declare-const Lemma_Unidirectional Bool)
;(assert
;  (= Lemma_Unidirectional
;     (=> (death_event 1 1))


; vim: ft=lisp:lw+=define-fun,forall,exists:
