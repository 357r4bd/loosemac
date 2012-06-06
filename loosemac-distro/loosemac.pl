#!/bin/env perl
use strict;
use Data::Dumper;

# To execute:
# % perl loosemac.pl < graph.dat

#
# This script serially simulates the simplest case that LooseMAC
# may be operating over.  That is, no nodes come or go and their
# links are stable.  Communication is done via a mailbox, and all
# state behaviors are dictated on a per node basis give the FSM
#

## Input file format
#
# num_nodes [optional_lambda]         # default lambda is number of nodes
# node1 (num_neighbors) n1 n2 n3 [slot1 slot2 slot3] # slots are optional
# ...
# noden (num_neighbors) n1 n2 n3 [slot1 slot2 slot3] # slots are optional
##

# logical constants
use constant TRUE  => 1;
use constant FALSE => 0;

# define msgs
use constant CORRUPTMSG      => -1;
use constant BEACONMSG       => 1;
use constant CONFLICTREPORT  => 2;
use constant BEACON_CONFLICT => 4;

my %reverse_msg_lookup = (
    '-1' => 'CORRUPTMSG',
    1    => 'BEACONMSG',
    2    => 'CONFLICTREPORT',
    4    => 'BEACON_CONFLICT',
);

# initialize variables
my $timestep       = 0;     # actual time count
my $lambda         = -1;    # initially unset; defaults to $num_nodes
my %when_ready     = ();    # tracks timestep that node a is ready
my %graph          = ();    # graph data structure
my $num_nodes      = 0;     # number of nodes in graph (network)
my %current_states = ();    # current state of all nodes
my %snd_hello      = ();    # tracks nodes "send beacon" bit
my %snd_error      = ();    # tracks nodes "send conflict report" bit
my %node_slot      = ();    # tracks currently selected sigma of each node
my %node_vectors   = ();    # tracks marking vector for each node
my %mailbox        = ();    # mailbox used at each timestep
my %default_slots  = ();    # holds default series of sigmas to assign a node; else they are random

# non-essential to protocol (for book keeping)
my $number_ready  = 0;      # number of ready nodes
my %notready_list = ();     # book keeping hash of not ready nodes
my %waiting_list  = ();     # book keeping hash of waiting nodes
my @ready_list    = ();     # array of nodes and when the are ready

# define states
use constant NOTREADY => 0;    # not waiting for CONFLICTREPORT, about to send BEACONMSG
use constant WAITING  => 1;    # sent BEACONMSG and waiting for CONFLICTREPORT
use constant READY    => 2;    # node has deemed itself ready

my %reverse_state_lookup = ( 0 => 'NOTREADY', 1 => 'WAITING', 2 => 'READY', );

# state table constants and transition definitions
use constant HEARDBEACON       => "A";
use constant SENTMSG           => "B";
use constant HEARDCONFLICT     => "C";
use constant DETECTEDCOLLISION => "D";
use constant WAITISOVER        => "E";

my %reverse_transition_lookup = (
    A => 'HEARDBEACON',
    B => 'SENTMSG',
    C => 'HEARDCONFLICT',
    D => 'DETECTEDCOLLISION',
    E => 'DETECTEDCOLLISION',
);

#
# Initiate and run simulation
#

&init;    #<- read in graph definition and perform initializations
&main;    #<- main timestepping loop

##
# Main timestepping loop
##

sub main {
    while (1) {
        $timestep++;
        my $slot = time2sigma($timestep);
        %mailbox = ();    # reset
        print STDERR "[ t=$timestep (slot=$slot) ]\n==================\n";

        # send messages
        send_msgs($timestep);

        # check mailbox and react accordingly
        check_mailbox($timestep);

        # make nodes "ready"
        check_ready($timestep);    # <- when should this be done? this affects things greatly
                                   # break out early when last is done
        print STDERR get_status_all();
        last if ( done() );
    }
}

#
# subroutines
#

##
# FSM definition and dispatcher
##

# given current state and input, runs referenced subroutine
sub state_machine_dispatch {
    my $node   = shift;
    my $symbol = shift;

    # get current state
    my $current_state = query_state($node);

    # gets references to the FSM function dispatch table
    my $mach_ref = get_machine();

    # call machine by reference to avoid duplication
    $mach_ref->{$current_state}{$symbol}->( $node, $symbol, @_ );
}

# creates a hash of hashes that contain subroutine references;
# it basically is a function table that executes a subroutine
# in the place of changing a state, though states are changed
# in the references subroutines
sub get_machine {
    my %machine = (
        0 =>
          { A => \&heard_beacon, B => \&sent_msg, C => \&nothing, D => \&detected_collision_noreset, E => \&nothing, },
        1 => {
            A => \&heard_beacon,
            B => \&nothing,
            C => \&heard_conflict,
            D => \&detected_collision_reset,
            E => \&make_ready,
        },
        2 => { A => \&nothing, B => \&nothing, C => \&nothing, D => \&nothing, E => \&nothing, },
    );
    return \%machine;
}

##
# init code
##

sub init {

    # reads initial graph; if default sigma is not set one is selected randomly
    # FORMAT:
    #
    #  number_of_nodes [framesize]
    #  foreach node
    #    node_number [inital_sigma] (num_neighbors) neigh1 neigh2 ... neighN
    #
    my $first = 0;

    # iterates over each line in the input file
    while (<>) {

        # $_ is the default variable containing the value of the line being processed
        $_ =~ s/#.*//g;     # clear out comments
        $_ =~ s/\s+/ /g;    # collapse multiple spaces into a single one
        if ( 1 == $. ) {
            chomp;          # get rid of the new line character at the end of the line
                            # first line - determine if lambda (frame size) is set here
            if ( $_ =~ m/^\s*([1-9][\d]*)(\s+\[([1-9][\d]*)\])?/ ) {
                $num_nodes = $1;

                # lambda defaults to number of nodes
                $lambda = $num_nodes;
                if ($3) {

                    # lambda updated if explicitly set
                    $lambda = $3;
                }
                print "$1 nodes in network\n";
                print "lambda set to: $lambda\n";
                $first++;
            }
        }
        elsif ( $_ =~ m/([\d]+)\s*\(([\d]+)\)\s*([\d\s]*)(\[([1-9][\d\s]*)\])*/ ) {

            #              1^^^^^^     2^^^^^^     3^^^^^^^^4^{5^^^^^^^^^^^^}^^^^
            # $1 -> node number
            my $node = $1;

            # $2 -> number of neighbors
            # $3 -> neighbor list (space delimited)
            # $4 -> ignore, outer optional pattern containing $5
            # $5 -> default series sigma slots to try for the node
            ## build neighbor listing
            $graph{$node} = [ split( ' ', $3 ) ];

            # initialize message bit queue
            mark_snd_hello($node);
            unmark_snd_error($node);

            # initialize default_slots
            $default_slots{$node} = [];

            # initialize all nodes into start state
            init_state($node);

            # adjust default slots based on lambda
            if ($5) {
                my @tmp = ();
                foreach my $slot ( split( ' ', $5 ) ) {
                    if ( $slot > $lambda ) {
                        $slot = $slot % $lambda;
                    }
                    push( @tmp, $slot );
                }
                if (@tmp) {
                    $default_slots{$node} = [@tmp];
                }
            }

            # assign initial slot
            get_new_slot($node);
        }
    }
}

##
# Message sending
##

sub send_msgs {
    my $timestep = shift;
    my $slot     = time2sigma($timestep);

    # for each node, send msg to each of its neighbors; detect and mark collisions
    foreach my $node ( sort { $a <=> $b } keys(%graph) ) {

        # send only if it is nodes turn and node is not "ready"
        if ( $slot == get_current_slot($node) && READY != query_state($node) ) {
            if ( !$snd_hello{$node} && $snd_error{$node} ) {
                foreach my $adj ( sort { $a <=> $b } @{ $graph{$node} } ) {
                    $mailbox{$adj} = { msg => CONFLICTREPORT, from => $node };
                    print "  $node: sent CONFLICTREPORT to $adj\n";
                }
                unmark_snd_error($node);
            }
            else {
                my %msg = ();
                if ( $snd_hello{$node} && !$snd_error{$node} ) {
                    $msg{msg}  = BEACONMSG;
                    $msg{from} = $node;
                }
                elsif ( $snd_hello{$node} && $snd_error{$node} ) {
                    $msg{msg}  = BEACON_CONFLICT;
                    $msg{from} = $node;
                }
                state_machine_dispatch( $node, SENTMSG, \%msg, \@{ $graph{$node} }, $timestep );
            }
        }
    }
    return;
}

##
# Message checking
##

sub check_mailbox {
    my $timestep = shift;
    foreach my $node ( sort { $a <=> $b } keys(%graph) ) {
        if ( exists( $mailbox{$node} ) ) {
            if ( CORRUPTMSG == $mailbox{$node}->{msg} ) {
                state_machine_dispatch( $node, DETECTEDCOLLISION );
            }
            elsif ( BEACONMSG == $mailbox{$node}->{msg} ) {
                state_machine_dispatch( $node, HEARDBEACON, $mailbox{$node}->{from}, $timestep );
            }
            elsif ( CONFLICTREPORT == $mailbox{$node}->{msg} ) {
                state_machine_dispatch( $node, HEARDCONFLICT, $mailbox{$node}->{from} );
            }
            elsif ( BEACON_CONFLICT == $mailbox{$node}->{msg} ) {
                state_machine_dispatch( $node, HEARDBEACON, $mailbox{$node}->{from}, $timestep );
                state_machine_dispatch( $node, HEARDCONFLICT, $mailbox{$node}->{from} );
            }
        }
    }
}

##
# Determine when to make a node ready
##

sub check_ready {
    my $timestep = shift;

    # for each node, send msg to each of its neighbors; detect and mark collisions
    foreach my $node ( sort { $a <=> $b } keys(%when_ready) ) {

        # send only if it is nodes turn and node is not "ready"
        state_machine_dispatch( $node, WAITISOVER, $timestep );
    }
}

##
# FSM event handlers
##

sub sent_msg {

    # -- require, default args
    my $node   = shift;
    my $symbol = shift;

    # --
    my $msg_ref  = shift;
    my $adj_ref  = shift;
    my $timestep = shift;

    # send message
    foreach my $adj ( sort { $a <=> $b } @{$adj_ref} ) {
        if ( !exists( $mailbox{$adj} ) ) {    # if no message is in the node's mailbox
            $mailbox{$adj} = $msg_ref;
        }
        else {
            $mailbox{$adj} = { msg => CORRUPTMSG, from => CORRUPTMSG };
        }
    }
    unmark_snd_hello($node);
    if ( BEACON_CONFLICT == $msg_ref->{msg} ) {
        unmark_snd_error($node);
    }
    my $slot          = time2sigma($timestep);
    my $readytimestep = $timestep + $lambda;
    print "  $node sent BEACONMESG to: ["
      . join( ',', @{$adj_ref} )
      . "] and will be ready @ next slot $slot (t=$readytimestep)\n";
    set_ready_time( $node, $readytimestep );
    change_state( $node, WAITING );
    return;
}

# does what is implies - nothing
sub nothing {

    # -- require, default args
    my $node   = shift;
    my $symbol = shift;

    # --
    return 1;
}

sub make_ready {

    # -- require, default args
    my $node   = shift;
    my $symbol = shift;

    # --
    my $timestep = shift;
    my $slot     = time2sigma($timestep);
    if ( exists( $when_ready{$node} ) ) {
        if ( $timestep == $when_ready{$node} ) {
            print "  $node is ready @ time $timestep (slot $slot)\n";
            change_state( $node, READY );
            $number_ready++;    # increment counter
                                # maybe reset messages waiting to be sent, but not sure yet
                                #...
        }
    }
    return;
}

sub heard_conflict {

    # -- require, default args
    my $node   = shift;
    my $symbol = shift;

    # --
    my $sender = shift;
    print "  $node: conflict report received from $sender\n";
    unset_ready_time($node);
    change_state( $node, NOTREADY );
    get_new_slot($node);

    # schedule beacon message
    mark_snd_hello($node);
}

sub detected_collision_noreset {

    # -- require, default args
    my $node   = shift;
    my $symbol = shift;

    # --
    print "  $node: detected collision\n";

    # needs to be done explicitly here
    mark_snd_error($node);
    return;
}

sub detected_collision_reset {

    # -- require, default args
    my $node   = shift;
    my $symbol = shift;

    # --
    detected_collision_noreset( $node, $symbol );
    unset_ready_time($node);
    change_state( $node, NOTREADY );
    get_new_slot($node);

    # schedule beacon message
    mark_snd_hello($node);
    return;
}

sub heard_beacon {

    # -- require, default args
    my $node   = shift;
    my $symbol = shift;

    # --
    my $sender   = shift;
    my $timestep = shift;
    my $slot     = time2sigma($timestep);
    print "  $node: heard beacon from $sender\n";

    # need to reset slot assignment for nodes trying again!
    if ( !manage_node_vectors( $node, $sender, $slot ) ) {
        print "  $node: detected marking conflict!\n";
        mark_snd_error($node);
    }
}

##
# Auxilary subs for handlers
##

sub manage_node_vectors {
    my $node   = shift;
    my $sender = shift;
    my $slot   = shift;
    my $ret    = FALSE;
    if ( !exists( $node_vectors{$node}{$slot} ) ) {

        # look to see if $from had previously reserved a slot here, if so delete
        for ( 1 .. $lambda ) {
            if ( $sender == $node_vectors{$node}{$_} ) {

                # delete old
                delete( $node_vectors{$node}{$_} );

                # break out of loop
                last;
            }
            elsif ( $node != $node_vectors{$node}{$slot} ) {
                $ret = TRUE;
            }
        }

        # set new
        $node_vectors{$node}{$slot} = $sender;
        $ret = TRUE;
    }
    return $ret;
}

sub set_ready_time {
    my $node          = shift;
    my $readytimestep = shift;
    $when_ready{$node} = $readytimestep;
}

sub unset_ready_time {
    my $node = shift;
    delete( $when_ready{$node} );
}

##
# State utilities
##

sub init_state {
    my $node = shift;
    change_state( $node, NOTREADY );
}

# given current state and message (as the symbol), set new state if there is one
sub change_state {
    my $node  = shift;
    my $state = shift;

    # clear $node from all lists
    delete( $notready_list{$node} ) if ( exists( $notready_list{$node} ) );
    delete( $waiting_list{$node} )  if ( exists( $waiting_list{$node} ) );

    # add back to proper one
    if ( NOTREADY == $state ) {
        $notready_list{$node}++;
    }
    elsif ( WAITING == $state ) {
        $waiting_list{$node}++;
    }
    elsif ( READY == $state ) {
        push( @ready_list, $node );
    }

    # finally, set state
    $current_states{$node} = $state;
}

sub query_state {
    my $node = shift;
    return $current_states{$node};
}

##
# Send message queue utilities
##

sub mark_snd_hello {
    my $node = shift;
    $snd_hello{$node} = TRUE;
}

sub unmark_snd_hello {
    my $node = shift;
    $snd_hello{$node} = FALSE;
}

sub mark_snd_error {
    my $node = shift;
    $snd_error{$node} = TRUE;
}

sub unmark_snd_error {
    my $node = shift;
    $snd_error{$node} = FALSE;
}

##
# Slot/Time management utilities
##

sub time2sigma {
    my $time = shift;
    if ( $time <= $lambda ) {
        return $time;
    }
    else {
        my $try = $time % $lambda + 1;
    }
}

# return random slot that is good as far as $node knows
sub get_random_free_slot {
    my $node = shift;
    my $try  = ( int( rand( $lambda - 1 ) ) + 1 );
    while ( exists( $node_vectors{$node}{$try} ) ) {
        $try = ( int( rand( $lambda - 1 ) ) + 1 );
    }
    return $try;
}

sub get_current_slot {
    my $node = shift;
    return $node_slot{$node};
}

sub set_current_slot {
    my $node = shift;
    my $slot = shift;
    $node_slot{$node} = $slot;
    return $slot;
}

# returns default if any are left, else returns random
sub get_new_slot {
    my $node = shift;
    my $how  = 'RANDOMLY';

    # delete $node's old slot as known to itself
    delete( $node_vectors{$node}{ get_current_slot($node) } );

    # select new slot
    if ( @{ $default_slots{$node} } ) {
        set_current_slot( $node, shift @{ $default_slots{$node} } );
        $how = 'EXPLICITLY';
    }
    else {
        set_current_slot( $node, get_random_free_slot($node) );
    }

    # make $node aware of its new slot
    $node_vectors{$node}{ get_current_slot($node) } = $node;

    # announce via
    print "  $node slot set $how to ", get_current_slot($node), "\n";
}

# status info reporting

sub get_status_all () {
    my $out = "  Nodal State Report [$number_ready / $num_nodes done]:\n";
    foreach ( sort { $a <=> $b } keys(%graph) ) {
        my $slot = 'with no slot assigned';

        $slot = "using slot $node_slot{$_}" if ( exists( $node_slot{$_} ) );

        $out .=
            "  Node $_ $slot is <"
          . $reverse_state_lookup{ $current_states{$_} }
          . "> Adjacent to ["
          . join( ',', @{ $graph{$_} } )
          . "]\n            Mail Queue: BEACON->[$snd_hello{$_}] CONFLICTREPORT->[$snd_error{$_}]\n";
    }
    $out .= "State tracking queues\n";
    $out .= "NOTREADY " . join( ',', sort { $a <=> $b } keys(%notready_list) ) . "\n";
    $out .= "WAITING  " . join( ',', sort { $a <=> $b } keys(%waiting_list) ) . "\n";
    $out .= "READY    " . join( ',', @ready_list ) . "\n";
    $out .= show_vectors();
    $out .= "==================\n";
    return $out;
}

sub show_vectors {
    my $out = "Node vectors\n";
    foreach my $node ( sort { $a <=> $b } keys(%node_vectors) ) {
        $out .= "$node {adjacent to: " . join( ',', @{ $graph{$node} } ) . "}:\n";
        foreach my $slot ( sort { $a <=> $b } keys( %{ $node_vectors{$node} } ) ) {
            my $self = '';
            $self = '*' if ( $node == $node_vectors{$node}{$slot} );
            $out .= "  slot $slot: $node_vectors{$node}{$slot}$self\n";
        }
    }
    $out .= "---\n";
    $out .= "* - self\n";
    return $out;
}

##
# Determines when the simulation is over
##

sub done {
    my $done = 0;

    # check for all done
    if ( $num_nodes == $number_ready ) {
        $done++;
        print STDERR "all ready in $timestep timesteps\n";
        print STDEER show_vectors();
    }

    # elsif(keys(%notready_list) && ! keys(%waiting_list))  { # requires some notready and NO waiting
    # my $num_locked = 0;
    # # check for situation where all of the neighbors of all of the nodes that are NOTREADY, are READY
    # # this couse an impossible situation that, and the nodes will never recover
    # foreach my $node (keys(%notready_list)) {
    #   my $locked = TRUE;
    #   foreach my $adj (@{$graph{$node}}) {
    #     if (READY != query_state($adj)) {
    #	  $locked = FALSE;
    #	  last;
    #       }
    #     }
    #     $num_locked ++ if ($locked);
    #   }
    #   if (keys(%notready_list) == $num_locked) {
    #     $done++;
    #   }
    # }

    return $done;
}
