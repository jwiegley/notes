(* It was: *)
Definition runMultiAssocWithCoastAndTerm (gap : MEt) (st : MHTState) (ws : list Waypoint) :
  MHTState :=
  if match st with
     | [] => true
     | hyp :: _ =>
       forallb (fun track =>
                  forallb (fun waypoint => MElt (time track) (timestamp waypoint)) ws)
               (liveTracks hyp)
     end
  then pruneGap score gap
                (runMHTUpdater (fun ts dts =>
                                  multiAssocWithCoastAndTerm ts dts ws no_filter_updater) st)
  else st.

(* Should be: *)
Definition runMultiAssocWithCoastAndTerm (st : MHTState) (ws : list Waypoint) :
  MHTState :=
  if match st with
     | [] => true
     | hyp :: _ =>
       forallb (fun track =>
                  forallb (fun waypoint => MElt (time track) (timestamp waypoint)) ws)
               (liveTracks hyp)
     end
  then pruneGap hypoScore (gapValue costs) (updateHypotheses ws st).
  else st.
