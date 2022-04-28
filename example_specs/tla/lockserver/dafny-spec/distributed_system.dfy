include "types.dfy"
include "network.dfy"
include "client.dfy"
include "server.dfy"
include "generic_definitions.dfy"

module System {
import opened Types
import opened Network
import opened Client_Agent
import opened Server_Agent
import opened Generic_Defs

datatype Constants = Constants(client_ids:seq<Id>, server_ids:seq<Id>)

predicate ValidTypes(c:Constants) {
    && (forall l | l in c.client_ids :: l.agt.C?)
    && (forall l | l in c.server_ids :: l.agt.S?)
}

predicate ValidServerIdx(c:Constants, i:int) {
    0<=i<|c.server_ids|
}

predicate ValidClientIdx(c:Constants, i:int) {
    0<=i<|c.client_ids|
}

predicate ValidServerId(c:Constants, id:Id) {
    id.agt == S && ValidServerIdx(c, id.idx)
}

predicate ValidClientId(c:Constants, id:Id) {
    id.agt == C && ValidClientIdx(c, id.idx)
}

predicate UniqueIds(c:Constants) {
    && seqIsUnique(c.client_ids)
    && seqIsUnique(c.server_ids)
}

predicate ValidIds(c:Constants) {
    && (forall i | ValidClientIdx(c, i) :: c.client_ids[i].idx == i)
    && (forall i | ValidServerIdx(c, i) :: c.server_ids[i].idx == i)
}

predicate WF(c:Constants) {
    && |c.client_ids| >= 1
    && |c.server_ids| >= 1
    && ValidTypes(c)
    && ValidIds(c)
    && UniqueIds(c)
}

datatype DistrSys = DistrSys(
    network: Environment,
    clients: seq<Client>,
    servers: seq<Server>
) 
    
predicate dsWF(c: Constants, ds:DistrSys) 
    requires WF(c)
{
    && |ds.clients| == |c.client_ids|
    && |ds.servers| == |c.server_ids|
    && (forall i | ValidClientIdx(c,i) :: ds.clients[i].consts.id == c.client_ids[i])
    && (forall i | ValidServerIdx(c,i) :: ds.servers[i].id == c.server_ids[i])
    && (forall i | ValidClientIdx(c,i) :: ds.clients[i].consts.servers == c.server_ids)
}

/*****************************************************************************************
*                                        DS Init                                         *
*****************************************************************************************/
predicate Init(c:Constants, ds:DistrSys) 
{
    && WF(c)
    && dsWF(c, ds)
    && EnvironmentInit(ds.network)
    && (forall i | ValidClientIdx(c,i) :: ClientInit(ds.clients[i], c.client_ids[i], c.server_ids))
    && (forall i | ValidServerIdx(c,i) :: ServerInit(ds.servers[i], c.server_ids[i]))
}


/*****************************************************************************************
*                                        DS Next                                         *
*****************************************************************************************/

predicate ValidActor(c:Constants, actor:Id) 
    requires WF(c)
{
     match actor.agt {
        case C => ValidClientIdx(c,actor.idx)
        case S => ValidServerIdx(c,actor.idx)
    }
}

predicate NextOneAgent(c:Constants, ds:DistrSys, ds':DistrSys, actor:Id, recvIo:IoOpt, sendIo:IoOpt)
    requires WF(c) && dsWF(c,ds) && dsWF(c,ds')
{
    && ValidActor(c, actor)
    && ds.network.nextStep == IoStep(actor, recvIo, sendIo)
    && EnvironmentNext(ds.network, ds'.network)
    && match actor.agt {
        case C => 
            && ds'.servers == ds.servers
            && ds'.clients == ds.clients[actor.idx := ds'.clients[actor.idx]]
            && ClientNext(ds.clients[actor.idx], ds'.clients[actor.idx], recvIo, sendIo)
        case S => 
            && ds'.clients == ds.clients
            && ds'.servers == ds.servers[actor.idx := ds'.servers[actor.idx]]
            && ServerNext(ds.servers[actor.idx], ds'.servers[actor.idx], recvIo, sendIo)
    }
}

predicate Next(c:Constants, ds:DistrSys, ds':DistrSys) {
    && WF(c)
    && dsWF(c, ds)
    && dsWF(c, ds')
    && exists actor, recvIo, sendIo :: NextOneAgent(c, ds, ds', actor, recvIo, sendIo)
}


/*****************************************************************************************
*                                        Safety                                          *
*****************************************************************************************/

/* Is this client in the Working state? */
predicate ClientIsWorking(cons:Constants, ds:DistrSys, cidx:int)
    requires WF(cons) && dsWF(cons, ds)
    requires ValidClientIdx(cons, cidx)
{
    ds.clients[cidx].state.Working?
}

/* Safety Property: No two clients can be working on the same server */
predicate Safety(cons:Constants, ds:DistrSys) 
    requires WF(cons) && dsWF(cons, ds)
{
    forall i, j | 
        && ValidClientIdx(cons, i)
        && ValidClientIdx(cons, j)
        && ClientIsWorking(cons, ds, i)
        && ClientIsWorking(cons, ds, j)
        && ds.clients[i].state.sid == ds.clients[j].state.sid
    ::
        i == j
}
}

/**
tla_Init == tla_s \in System_DistrSys /\ System_Init(tla_c, tla_s)
tla_Next == tla_s' \in System_DistrSys /\ System_Next(tla_c, tla_s, tla_s')
tla_Spec == tla_Init /\ [][tla_Next]_(tla_s)

tla_Safety == System_Safety(tla_c, tla_s)
**/