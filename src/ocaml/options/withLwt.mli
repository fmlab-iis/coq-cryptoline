
val unix : string -> Lwt_unix.process_status Lwt.t
val trace : string -> unit Lwt.t
(* Same as trace but without appending a newline *)
val tracen : string -> unit Lwt.t
val trace_file : string -> unit Lwt.t
val fail : string -> 'a Lwt.t

val lock_log : unit -> unit Lwt.t
val unlock_log : unit -> unit
