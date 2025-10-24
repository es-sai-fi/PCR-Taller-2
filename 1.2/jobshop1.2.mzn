include "cumulative.mzn";

% ---- Parameters ----
float: weight_makespan;                          % Weight given to makespan minimization  
float: weight_load_balancing;                    % Weight given to load balancing
int: jobs;                                       % Number of jobs
set of int: JOB = 1..jobs;
int: tasks;                                      % Number of tasks per job
set of int: TASK = 1..tasks;
int: k;                                          % Number of workers
set of int: WORKER = 1..k;
array [JOB, TASK] of int: d;                     % Task durations
int: total = sum(i in JOB, j in TASK) (d[i, j]); % Total duration
int: digs = ceil(log(10.0, total));              % Digits for output
float: mean_load = total / k;

% ---- Variables and Domains ----
array [JOB, TASK] of var 0..total: s;            % Start times
var 0..total: end;                               % Total end time
array [JOB, TASK] of var WORKER: w;              % Worker assignation
array [WORKER] of var 0..total: load;            % Work load for each worker
var int: load_range = max(load) - min(load);     % Difference between max and min load

% ---- Helper Functions ----
predicate no_overlap(var int:s1, int:d1, var int:s2, int:d2) =
    s1 + d1 <= s2 \/ s2 + d2 <= s1;

% ---- Constraints ----
% Tasks are executed sequentially
constraint forall(i in JOB) (
  forall(j in 1..tasks-1) (
    s[i, j] + d[i, j] <= s[i, j+1]) /\ s[i, tasks] + d[i, tasks] <= end
);

% No overlapping
constraint forall(j in TASK) (
  forall(i, v in JOB where i < v) (
    no_overlap(s[i, j], d[i, j], s[v, j], d[v, j])
  )
);
    
% Worker usage global limit
constraint cumulative(
    [s[i, j] | i in JOB, j in TASK],
    [d[i, j] | i in JOB, j in TASK],
    [1 | i in JOB, j in TASK],
    k
);

% A worker can only be used for 1 task at a time
constraint forall(i1 in JOB, j1 in TASK, i2 in JOB, j2 in TASK where (i1, j1) < (i2, j2)) (
  (w[i1, j1] = w[i2, j2]) -> no_overlap(s[i1, j1], d[i1, j1], s[i2, j2], d[i2, j2])
);

% Worker load calculation
constraint forall(p in WORKER) (
  load[p] = sum(i in JOB, j in TASK where w[i, j] = p) (d[i, j])
);

% No worker should exceed the mean load
%constraint forall(p in WORKER) (
%  load[p] <= ceil(mean_load)
%);

% ---- Redundant Constraints ----
% Lower and upper bound for a worker's load
constraint forall(p in WORKER) ( 0 <= load[p] /\ load[p] <= total );

% End time should always be greater or equal to each task duration
constraint forall(i in JOB, j in TASK) (
  end >= s[i,j] + d[i,j]
);

% ---- Symmetry Breaking ----
% Workers ordered by load (identical workers)
%constraint forall(p in 1..k-1) (
%  load[p] <= load[p+1]
%);

% Tasks ordered by start time (identical jobs)
% constraint if forall(i in JOB, j in TASK where i < jobs) (
%  forall(u in TASK) (d[i, u] = d[i+1, u])
%) then
%  forall(v in 1..jobs-1) (
%    s[v, 1] <= s[v+1, 1]
%  )
%else
%  true
%endif;

% ---- Solve ----
solve :: int_search([s[i, j] | i in JOB, j in TASK] ++ [w[i, j] | i in JOB, j in TASK], first_fail, indomain_min, complete)
%solve :: int_search([w[i, j] | i in JOB, j in TASK] ++ [s[i, j] | i in JOB, j in TASK], first_fail, indomain_min, complete)
%solve :: int_search([w[i, j] | i in JOB, j in TASK] ++ [s[i, j] | i in JOB, j in TASK], dom_w_deg, indomain_min, complete)
%solve :: int_search([s[i, j] | i in JOB, j in TASK] ++ [w[i, j] | i in JOB, j in TASK], dom_w_deg, indomain_min, complete)
minimize ((end - total / k) / (total - total / k)) * weight_makespan 
         + (load_range / total) * weight_load_balancing;

% ---- Output ----
output [
  "Makespan: \(end)\n",
  "Schedule:\n"
] ++
[
  "Job \(i), Task \(j): Machine \(j), Start=\(s[i,j]), End=\(s[i,j]+d[i,j]), Worker=\(w[i,j])\n"
  | i in JOB, j in TASK
] ++
[
  "\nWorker loads: " ++ show([load[p] | p in WORKER]) ++ "\n",
  "Gantt Chart:\n"
] ++
[
  if j == 1 then "Job \(i): " else "" endif ++
  "M\(j):\(s[i,j])..\(s[i,j]+d[i,j]) " ++
  if j == tasks then "\n" else "" endif
  | i in JOB, j in TASK
];
