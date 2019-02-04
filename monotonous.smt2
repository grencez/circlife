
(set-option :produce-models true)

(declare-fun planet (Int Int) Int)
(declare-fun population_size (Int) Int)
(assert (> (population_size 0) 0))
(assert (= (planet 0 0)
           (planet 0 (population_size 0))))

;; The step when the cell at index 0 dies.
;; We do not bother modeling that step.
(declare-const Lifespan Int)
(assert (> Lifespan 0))

(declare-fun spawn (Int) Int)
(declare-fun death (Int) Int)

(assert
  (forall ((t Int))
    (=> (and (> t 0) (< t Lifespan))
        (and
          (or (= (spawn t) 0)
              (= (death t) 0))
          (or (> (spawn t) 0)
              (> (death t) 0))
          (and (<= (spawn t) (population_size (- t 1)))
               (<  (death t) (population_size (- t 1))))))))
(assert
  (forall ((t Int))
    (=> (and (> t 0) (< t Lifespan)
             (> (spawn t) 0))
        (= (population_size t)
           (+ (population_size (- t 1)) 1)))))

(assert
  (forall ((t Int))
    (=> (and (> t 0) (< t Lifespan)
             (> (death t) 0))
        (= (population_size t)
           (- (population_size (- t 1)) 1)))))

(push)
(echo "######################################################################")
(echo "Verifying that the population always grows or shrinks by 1.")
(echo "(expect unsat)")
(declare-const t Int)
(assert (and (> t 0) (< t Lifespan)))
;;;; For a contradiction, assume:
(assert
  (not (or (= (population_size t)
              (- (population_size (- t 1)) 1))
           (= (population_size t)
              (+ (population_size (- t 1)) 1)))))
(check-sat)
(pop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; How cells shift as time progresses.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert
  (forall ((t Int) (i Int))
    (=> (and (> t 0) (< t Lifespan) (>= i 0)
             (or (< i (spawn t))
                 (< i (death t))))
        (= (planet t i) (planet (- t 1) i)))))


(define-fun Lemma_CellOfInterestAtIndexZero ((t Int)) Bool
  (=> (and (>= t 0) (< t Lifespan))
      (= (planet t 0) (planet 0 0))))
(push)
(echo "######################################################################")
(echo "Verifying that the cell of interest is copied throughout its lifetime.")
(echo "(expect unsat)")
(define-fun Assumptions ((t Int)) Bool
  (and (>= t 0) (< t Lifespan)))
(define-fun Predicate ((t Int)) Bool
  (Lemma_CellOfInterestAtIndexZero t))
(declare-const t Int)
(push)
(assert (Assumptions t))
;;;; For a contradiction, assume:
(assert (not (Predicate t)))
;;;; Inductive base.
(push)
(assert (<= t 0))
(check-sat)
(pop)
;;;; Inductive step.
(assert (> t 0))
(assert (Predicate (- t 1)))
(check-sat) (pop)
(assert (=> (Assumptions t) (Predicate t)))
(assert (not (Lemma_CellOfInterestAtIndexZero t)))
(check-sat)
(pop)
;;;; Proved.
(assert (forall ((t Int))
          (Lemma_CellOfInterestAtIndexZero t)))


(assert
  (forall ((t Int) (i Int))
    (=> (and (> t 0) (< t Lifespan)
             (> (spawn t) 0)
             (>= i (spawn t)) (<= i (population_size (- t 1))))
        (= (planet t (+ i 1))
           (planet (- t 1) i)))))

(assert
  (forall ((t Int) (i Int))
    (=> (and (> t 0) (< t Lifespan)
             (> (death t) 0)
             (> i (death t)) (<= i (population_size (- t 1))))
        (= (planet t (- i 1))
           (planet (- t 1) i)))))


(define-fun Lemma_CellOfInterestAtLastIndex ((t Int)) Bool
  (=> (and (>= t 0) (< t Lifespan))
      (= (planet t (population_size t )) (planet 0 0))))
(push)
(echo "######################################################################")
(echo "Verifying that the cell of interest is copied to the rightmost cell.")
(echo "(expect unsat)")
(define-fun Assumptions ((t Int)) Bool
  (and (>= t 0) (< t Lifespan)))
(define-fun Predicate ((t Int)) Bool
  (Lemma_CellOfInterestAtLastIndex t))
(declare-const t Int)
(push)
(assert (Assumptions t))
;;;; For a contradiction, assume:
(assert (not (Predicate t)))
;;;; Inductive base.
(push)
(assert (<= t 0))
(check-sat)
(pop)
;;;; Inductive step.
(assert (> t 0))
(assert (Predicate (- t 1)))
(check-sat)
(pop)
(assert (=> (Assumptions t) (Predicate t)))
(assert (not (Lemma_CellOfInterestAtLastIndex t)))
(pop)
;;;; Proved.
(assert (forall ((t Int))
          (Lemma_CellOfInterestAtLastIndex t)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Spawning Relation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Whether a cell with the middle given genome can result from
;; cells with the given left and right genomes spawning.
(declare-fun spawnable (Int Int Int) Bool)

;;; Whether a cell can result from cells with the given genomes spawning.
;(declare-fun compatible (Int Int) Bool)
(define-fun compatible ((p Int) (q Int)) Bool
  (exists ((c Int))
    (spawnable p c q)))

;; Incompatible with parents.
(assert
  (forall ((p Int) (c Int) (q Int))
    (=> (spawnable p c q)
        (and (not (compatible p c))
             (not (compatible c q))))))

;; Incompatible with grandparents.
(assert
  (forall ((g Int) (p Int) (c Int)  (q Int) (h Int))
    (=> (and (spawnable g p h)
             (spawnable p c q))
        (and (not (compatible g c))
             (not (compatible c h))))))

;; This is how spawning works.
(assert
  (forall ((t Int))
    (=> (and (> t 0) (< t Lifespan) (> (spawn t) 0))
        (spawnable (planet t (- (spawn t) 1))
                   (planet t (spawn t))
                   (planet t (+ (spawn t) 1))))))


(declare-fun population_potential_rec (Int Int) Int)
(define-fun population_potential ((t Int)) Int
  (population_potential_rec t (population_size t)))

(assert
  (forall ((t Int))
    (=> (and (>= t 0) (< t Lifespan))
        (= (population_potential_rec t 0) 0))))

(assert
  (forall ((t Int) (i Int))
    (=> (and (>= t 0) (< t Lifespan) (> i 0) (<= i (population_size t)))
        (= (population_potential_rec t i)
           (+ (ite (compatible (planet t (- i 1)) (planet t i))
                   1 0)
              (population_potential_rec t (- i 1)))))))


(push)
(echo "######################################################################")
(echo "Verifying that population potential is less than or equal to its actual size.")
(echo "(expect unsat)")
(define-fun Predicate ((t Int) (i Int)) Bool
  (<= (population_potential_rec t i)
      i))
(declare-const t Int)
(declare-const i Int)
(assert (and (>= t 0) (< t Lifespan)
             (>= i 0) (<= i (population_size t))))
;;;; For a contradiction, assume:
(assert (not (Predicate t i)))
;;;; Inductive base.
(push)
(assert (<= i 0))
(check-sat)
(pop)
;;;; Inductive step.
(assert (> i 0))
(assert (Predicate t (- i 1)))
(check-sat)
(pop)


(define-fun Lemma_SpawnDecreasesPopulationPotentialByOne ((t Int)) Bool
  (=> (and (> t 0) (< t Lifespan) (> (spawn t) 0))
      (<= (population_potential t)
          (- (population_potential (- t 1)) 1))))
(push)
(echo "######################################################################")
(echo "Verifying that a spawn decreases the population potential by 1.")
(echo "(expect unsat)")
(define-fun Assumptions ((t Int) (i Int)) Bool
  (and (> t 0) (< t Lifespan)
       (> (spawn t) 0)
       (> i 0) (<= i (population_size t))))
(define-fun Predicate ((t Int) (i Int)) Bool
  (and
    (=> (< i (spawn t))
        (= (population_potential_rec t i)
           (population_potential_rec (- t 1) i)))
    (=> (= i (spawn t))
        (= (population_potential_rec t i)
           (- (population_potential_rec (- t 1) i) 1)))
    (=> (> i (spawn t))
        (= (population_potential_rec t i)
           (- (population_potential_rec (- t 1) (- i 1)) 1)))))

(declare-const t Int)

(push)
(declare-const i Int)
(assert (Assumptions t i))
;;;; For a contradiction, assume:
(assert (not (Predicate t i)))
;;;; Inductive base.
(push)
(assert (<= i 2))
(check-sat)
(pop)
;;;; Inductive step.
(assert (> i 2))
(assert (Predicate t (- i 1)))
(check-sat)
(pop)

(assert (forall ((i Int))
          (=> (Assumptions t i)
              (Predicate t i))))
(assert (not (Lemma_SpawnDecreasesPopulationPotentialByOne t)))
(check-sat)
(pop)
;;;; Proved.
(assert (forall ((t Int))
          (Lemma_SpawnDecreasesPopulationPotentialByOne t)))



(define-fun Lemma_DeathIncreasePopulationPotentialByAtMostOne ((t Int)) Bool
  (=> (and (> t 0) (< t Lifespan) (> (death t) 0))
      (<= (population_potential t)
          (+ (population_potential (- t 1)) 1))))
(push)
(echo "######################################################################")
(echo "Verifying that a death at most increases the population potential by 1.")
(echo "(expect unsat)")
(define-fun Assumptions ((t Int) (i Int)) Bool
  (and (> t 0) (< t Lifespan)
       (> (death t) 0)
       (> i 0) (<= i (population_size t))))
(define-fun Predicate ((t Int) (i Int)) Bool
  (and
    (=> (< i (death t))
        (= (population_potential_rec t i)
           (population_potential_rec (- t 1) i)))
    (=> (>= i (death t))
        (<= (population_potential_rec t i)
            (+ (population_potential_rec (- t 1) (+ i 1)) 1)))))
(declare-const t Int)

(push)
(declare-const i Int)
(assert (Assumptions t i))

;;;; For a contradiction, assume:
(assert (not (Predicate t i)))
;;;; Inductive base.
(push)
(assert (<= i 2))
(check-sat)
(pop)
;;;; Inductive step.
(assert (> i 2))
(assert (Predicate t (- i 1)))
(check-sat)
(pop)

(assert (forall ((i Int))
          (=> (Assumptions t i)
              (Predicate t i))))
(assert (not (Lemma_DeathIncreasePopulationPotentialByAtMostOne t)))
(check-sat)
(pop)
;;;; Proved.
(assert (forall ((t Int))
          (Lemma_DeathIncreasePopulationPotentialByAtMostOne t)))


(define-fun Lemma_NonIncreasingPopulationSizePlusPotential ((t Int)) Bool
  (=> (and (> t 0) (< t Lifespan))
      (<= (+ (population_size t) (population_potential t))
          (+ (population_size (- t 1)) (population_potential (- t 1))))))
(push)
(echo "######################################################################")
(echo "Verifying that the sum of population size and potential is non-increasing.")
(echo "(expect unsat)")
(declare-const t Int)
(assert (not (Lemma_NonIncreasingPopulationSizePlusPotential t)))
(check-sat)
(pop)
(assert (forall ((t Int))
          (Lemma_NonIncreasingPopulationSizePlusPotential t)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sustainability.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In order to sustain life, the population size plus its potential cannot ever
;; decrease. This sum cannot increase, so any decrease would be permanent.
(define-fun SustainedLife ((t Int)) Bool
  (=> (and (> t 0) (< t Lifespan))
      (= (+ (population_size t) (population_potential t))
         (+ (population_size (- t 1)) (population_potential (- t 1))))))

(define-fun Lemma_SustainableDeath ((t Int)) Bool
  (=> (and (> t 0) (< t Lifespan)
           (SustainedLife t)
           (> (death t) 0))
      (and
        (not (compatible (planet (- t 1) (- (death t) 1))
                         (planet (- t 1) (death t))))
        (not (compatible (planet (- t 1) (death t))
                         (planet (- t 1) (+ (death t) 1))))
        (compatible (planet (- t 1) (- (death t) 1))
                    (planet (- t 1) (+ (death t) 1))))))
(push)
(echo "######################################################################")
(echo "Verifying that each cell that dies must be incompatible with its neighbors,")
(echo "and those neighbors must be compatible with each other if life is sustained.")
(echo "(expect unsat)")
(define-fun Assumptions ((t Int) (i Int)) Bool
  (and (> t 0) (< t Lifespan)
       (> (death t) 0)
       (> i 0) (<= i (population_size t))
       (or (compatible (planet (- t 1) (- (death t) 1))
                       (planet (- t 1) (death t)))
           (compatible (planet (- t 1) (death t))
                       (planet (- t 1) (+ (death t) 1)))
           (not (compatible (planet (- t 1) (- (death t) 1))
                            (planet (- t 1) (+ (death t) 1)))))))
(define-fun Predicate ((t Int) (i Int)) Bool
  (and
    (=> (< i (death t))
        (= (population_potential_rec t i)
           (population_potential_rec (- t 1) i)))
    (=> (>= i (death t))
        (<= (population_potential_rec t i)
            (population_potential_rec (- t 1) (+ i 1))))))
(declare-const t Int)

(push)
(declare-const i Int)
(assert (Assumptions t i))

;;;; For a contradiction, assume:
(assert (not (Predicate t i)))
;;;; Inductive base.
(push)
(assert (<= i 1))
(check-sat)
(pop)
(assert (Predicate t 1))
(push)
(assert (= i 2))
(check-sat)
(pop)
(assert (Predicate t 2))
;;;; Inductive step.
(assert (> i 2))
(assert (Predicate t (- i 1)))
(check-sat)
(pop)

(assert (forall ((i Int))
          (=> (Assumptions t i)
              (Predicate t i))))
(assert (not (Lemma_SustainableDeath t)))
(check-sat)
(pop)
;;;; Proved.
(assert (forall ((t Int))
          (Lemma_SustainableDeath t)))


; vim: ft=lisp:lw+=define-fun,forall,exists:
