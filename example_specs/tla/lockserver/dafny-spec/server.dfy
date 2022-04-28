include "types.dfy"
include "network.dfy"

module Server_Agent {
import opened Types
import opened Network

datatype ResourceStatus = Free | Held(client:Id)

datatype Server = Server(
    id:Id,                  
    resource:ResourceStatus,    // is this server free to grant requests?
    epoch_map:map<Id, Epoch>    // maps each client to the latest epoch seen from that client
)


/* Server taking a stutter step */
predicate ServerStutter(s:Server, s':Server, sendIo:IoOpt) {
    && s' == s
    && sendIo == None
}

/* Server initial state */
predicate ServerInit(s:Server, id:Id) {
    && s.id == id
    && s.resource.Free?
    && s.epoch_map == map[]
}


predicate ProcessRequest_Grant(s:Server, s':Server, p:Packet, sendIo:IoOpt) 
    requires p.msg.Request?
{
    && s'.epoch_map == s.epoch_map[p.src := p.msg.e]
    && s'.resource == Held(p.src)
    && sendIo == Some(Packet(s.id, p.src, Grant(p.msg.e)))
}

predicate ProcessRequest_Reject(s:Server, s':Server, p:Packet, sendIo:IoOpt) 
    requires p.msg.Request?
{
    && s'.epoch_map == s.epoch_map
    && s'.resource == s.resource
    && sendIo == Some(Packet(s.id, p.src, Reject(p.msg.e)))
}


/* Server processing a Request message from a client */
predicate ProcessRequest(s:Server, s':Server, recvIo:IoOpt, sendIo:IoOpt) 
    requires recvIo.Some? && recvIo.p.msg.Request?
{
    var e := recvIo.p.msg.e;
    if !s.resource.Free? then
        ProcessRequest_Reject(s, s', recvIo.p, sendIo)
    //Bug 2: conditional was like the following. This is a liveness bug, as s.epoch_map 
    // starts of as empty.
    // else if && recvIo.p.src in s.epoch_map 
    //         &&  e > s.epoch_map[recvIo.p.src] then
    else if 
        recvIo.p.src !in s.epoch_map ||
        (   && recvIo.p.src in s.epoch_map 
            &&  e > s.epoch_map[recvIo.p.src] ) then
        ProcessRequest_Grant(s, s', recvIo.p, sendIo)
    else 
        ProcessRequest_Reject(s, s', recvIo.p, sendIo)
}



predicate ProcessRelease_Release(s:Server, s':Server, sendIo:IoOpt) {
    && s'.epoch_map == s.epoch_map
    && s'.resource == Free
    && sendIo == None
}


/* Server processing a Release message from a client */
predicate ProcessRelease(s:Server, s':Server, recvIo:IoOpt, sendIo:IoOpt) 
    requires recvIo.Some? && recvIo.p.msg.Release?
{
    var e := recvIo.p.msg.e;
    if s.resource.Free? then 
        ServerStutter(s, s', sendIo)
    else if && s.resource.client == recvIo.p.src 
            && recvIo.p.src in s.epoch_map
            && s.epoch_map[recvIo.p.src] == e then
        ProcessRelease_Release(s, s, sendIo)
    else
        ServerStutter(s, s', sendIo)
}


/* Server next state */
predicate ServerNext(s:Server, s':Server, recvIo:IoOpt, sendIo:IoOpt) 
{
    && recvIo.Some? 
    && s'.id == s.id
    && match recvIo.p.msg {
        case Request(e) => ProcessRequest(s, s', recvIo, sendIo)
        case Release(e) => ProcessRelease(s, s', recvIo, sendIo)
        case _ => ServerStutter(s, s', sendIo)
    }
}

}