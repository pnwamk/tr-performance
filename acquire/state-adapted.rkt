#lang typed/racket

;; ---------------------------------------------------------------------------------------------------
;; a data representation for internal game states 
;; -- inspecting the game state 
;; -- manipulating the game state 
;; including a data structure for internalizing the state of the players

(require
 "board-adapted.rkt"
 "types.rkt"
 typed/racket/class)

(require "state.rkt")
(define-type State state)
(define-type Player player)

;; -----------------------------------------------------------------------------

(define-type Decisions (Listof (List Player (Listof (List Hotel Boolean)))))
(define-type Score (Listof (List String Cash)))

(define-type Administrator%
  (Class
   (init-field
    (next-tile (-> (Listof Tile) Tile)))
   (sign-up (-> String (Instance Player%) String))
   (show-players (-> (Listof String)))
   (run (->* (Natural) (#:show (-> Void)) RunResult))
   ))

(define-type Turn%
  (Class
   (init-field (current-state State))
   (field
    (board Board)
    (current Player)
    (cash Cash)
    (tiles (Listof Tile))
    (shares Shares)
    (hotels (Listof Hotel))
    (players (Listof Player)))
   (reconcile-shares (-> Shares Shares))
   (eliminated (-> (Listof Player)))
   (place-called (-> Boolean))
   (decisions (-> (Values (Option Tile) (Option Hotel) Decisions)))
   ;; Precondition: (send this place-called)
   (place (-> Tile Hotel (U Void (Listof Player))))
   ))

(define-type Player%
  (Class
   (init-field
    [name String]
    [choice Strategy])
   (field
    [*players (Listof Player)]
    [*bad (Listof Player)])
   (go (-> (Instance Administrator%) Void))
   (setup (-> State Void))
   (take-turn (-> (Instance Turn%) (Values (Option Tile) (Option Hotel) (Listof Hotel))))
   (keep (-> (Listof Hotel) (Listof Boolean)))
   (receive-tile (-> Tile Void))
   (inform (-> State Void))
   (the-end (-> State Any Void))))

(define-type RunResult (List (U 'done 'exhausted 'score 'IMPOSSIBLE) Any (Listof State)))
(define-type Strategy (-> (Instance Turn%) (Values (Option Tile) (Option Hotel) (Listof Hotel))))

;; -----------------------------------------------------------------------------

(provide
 player?
 player-money
 player-tiles
 player-shares
 player-external
 player-name
 player0
 *create-player
 state?
 state-hotels
 state-shares
 state-sub-shares
 state-tiles
 state-board
 state-players
 state-current-player
 state0
 state-place-tile
 state-buy-shares
 state-return-shares
 state-move-tile
 state-next-turn
 state-remove-current-player
 state-eliminate
 state-score
 state-final?
 *create-state
 *cs0
 ;; --
 Score
 Player
 State
 Decisions
 ;; --
 Administrator%
 Turn%
 Player%
 RunResult
 Strategy
)

