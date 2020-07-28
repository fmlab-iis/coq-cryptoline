
open Std

let unix cmd = Lwt_unix.system cmd

let trace msg =
  if !debug then
    let%lwt _ = unix ("echo \"" ^ msg ^ "\n\" >> " ^ !logfile) in
    Lwt.return()
  else
    Lwt.return()

let tracen msg =
  if !debug then
    let%lwt _ = unix ("echo \"" ^ msg ^ "\" >> " ^ !logfile) in
    Lwt.return()
  else
    Lwt.return()

let trace_file file =
  if !debug then
    let%lwt _ = unix ("cat " ^ file ^ " >>  " ^ !logfile) in
    Lwt.return()
  else
    Lwt.return()

let fail s = let%lwt _ = trace s in failwith s

let mutex = Lwt_mutex.create ()

let lock_log () = Lwt_mutex.lock mutex
let unlock_log () = Lwt_mutex.unlock mutex
