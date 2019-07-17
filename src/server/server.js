/*jslint bitwise: true, node: true */
'use strict';

// 0.1. Web-framework
var express = require('express');
var app = express();
// 0.2. Http-web-framework
var http = require('http').Server(app);
// 0.3. Socket-server
var io = require('socket.io')(http);
// 0.4. 2D-Collision-detection based on: Separating Axis Theorem
var SAT = require('sat');
var sql = require ("mysql");

// Import game settings.
var c = require('../../config.json');

// Import utilities.
var util = require('./lib/util');

// Import quadtree.
var quadtree = require('simple-quadtree');

//call sqlinfo
var s = c.sqlinfo;

// Quadtree to reduce number of collision checking
var tree = quadtree(0, 0, c.gameWidth, c.gameHeight);

// State.1. list of user
var users = [];
// State.2. list of mass-food - coming out from player
var massFood = [];
// State.3. list of food in game
var food = [];
// State.4. list of virus in game
var virus = [];
// Stats.5. map of socket by player
var sockets = {};
// State.6. top-player in leaderboard
var leaderboard = [];
var leaderboardChanged = false;

// SAT-point
var V = SAT.Vector;
// SAT-circle - in this game-logic - only detect collision between circle
var C = SAT.Circle;

if(s.host !== "DEFAULT") {
    var pool = sql.createConnection({
        host: s.host,
        user: s.user,
        password: s.password,
        database: s.database
    });

    //log sql errors
    pool.connect(function(err){
        if (err){
            console.log (err);
        }
    });
}

var initMassLog = util.log(c.defaultPlayerMass, c.slowBase);

app.use(express.static(__dirname + '/../client'));

/**
 * Add more food to game
 * @param {number of food to add to game} toAdd 
 */
function addFood(toAdd) {
    var radius = util.massToRadius(c.foodMass);
    while (toAdd--) {
        var position = c.foodUniformDisposition ? util.uniformPosition(food, radius) : util.randomPosition(radius);
        food.push({
            // Make IDs unique.
            id: ((new Date()).getTime() + '' + food.length) >>> 0,
            x: position.x,
            y: position.y,
            radius: radius,
            mass: Math.random() + 2,
            hue: Math.round(Math.random() * 360)
        });
    }
}

/**
 * Add more virus to game
 * @param {number of virus to add to game} toAdd 
 */
function addVirus(toAdd) {
    while (toAdd--) {
        var mass = util.randomInRange(c.virus.defaultMass.from, c.virus.defaultMass.to, true);
        var radius = util.massToRadius(mass);
        var position = c.virusUniformDisposition ? util.uniformPosition(virus, radius) : util.randomPosition(radius);
        virus.push({
            id: ((new Date()).getTime() + '' + virus.length) >>> 0,
            x: position.x,
            y: position.y,
            radius: radius,
            mass: mass,
            fill: c.virus.fill,
            stroke: c.virus.stroke,
            strokeWidth: c.virus.strokeWidth
        });
    }
}

/**
 * Remove food
 * @param {number of food to remove} toRem 
 */
function removeFood(toRem) {
    while (toRem--) {
        food.pop();
    }
}

/**
 * Moving a player
 * @param {moving player as movement-parameters} player 
 */
function movePlayer(player) {
    var x =0,y =0;
    // 1. Moving all player-cells
    for(var i=0; i<player.cells.length; i++)
    {
        // 1.0. the player.target attribute is the target vector from player to target-point
        // 1.1. the target of this cell - calculate from the target of the player
        var target = {
            x: player.x - player.cells[i].x + player.target.x,
            y: player.y - player.cells[i].y + player.target.y
        };
        // 1.2. distance from cell to target-point
        var dist = Math.sqrt(Math.pow(target.y, 2) + Math.pow(target.x, 2));
        // 1.3. angle from cell to target-point
        var deg = Math.atan2(target.y, target.x);
        // 1.4. moving velocity
        var slowDown = 1;
        if(player.cells[i].speed <= 6.25) {
            slowDown = util.log(player.cells[i].mass, c.slowBase) - initMassLog + 1;
        }
        // 1.5. moving delta
        var deltaY = player.cells[i].speed * Math.sin(deg)/ slowDown;
        var deltaX = player.cells[i].speed * Math.cos(deg)/ slowDown;

        if(player.cells[i].speed > 6.25) {
            player.cells[i].speed -= 0.5;
        }
        if (dist < (50 + player.cells[i].radius)) {
            deltaY *= dist / (50 + player.cells[i].radius);
            deltaX *= dist / (50 + player.cells[i].radius);
        }
        if (!isNaN(deltaY)) {
            player.cells[i].y += deltaY;
        }
        if (!isNaN(deltaX)) {
            player.cells[i].x += deltaX;
        }


        // 
        /*
        --> Should update this logic in future-dev
        Consider player-cells from bigger mass to smaller mass 
        moving the bigger-cell first
        + other smaller cell can consider to merge to bigger cell 
        if smaller cell merged --> remove from list --> not need to update move 
        + compare the position to bigger cell - and also moving closer to bigger cell
        do not use logic move close to every other cell
        + the player position is the average position of all cells that not merged 
        */
        // 1.6. Make player-cells close to each other
        // can build other solution - but this is a simple solution
        // simply check all other-cells - then moving current cell a little bit to other cell
        // Find best solution.
        for(var j=0; j<player.cells.length; j++) {
            if(j != i && player.cells[i] !== undefined) {
                var distance = Math.sqrt(
                    Math.pow(player.cells[j].y-player.cells[i].y,2) + Math.pow(player.cells[j].x-player.cells[i].x,2)
                    );

                var radiusTotal = (player.cells[i].radius + player.cells[j].radius);
                if(distance < radiusTotal) {
                    if(player.lastSplit > new Date().getTime() - 1000 * c.mergeTimer) {
                        if(player.cells[i].x < player.cells[j].x) {
                            player.cells[i].x--;
                        } else if(player.cells[i].x > player.cells[j].x) {
                            player.cells[i].x++;
                        }
                        if(player.cells[i].y < player.cells[j].y) {
                            player.cells[i].y--;
                        } else if((player.cells[i].y > player.cells[j].y)) {
                            player.cells[i].y++;
                        }
                    }
                    else if(distance < radiusTotal / 1.75) {
                        player.cells[i].mass += player.cells[j].mass;
                        player.cells[i].radius = util.massToRadius(player.cells[i].mass);
                        player.cells.splice(j, 1);
                    }
                }
            }
        }

        // 1.7. Make cell not move out of the border to much
        if(player.cells.length > i) {
            var borderCalc = player.cells[i].radius / 3;
            if (player.cells[i].x > c.gameWidth - borderCalc) {
                player.cells[i].x = c.gameWidth - borderCalc;
            }
            if (player.cells[i].y > c.gameHeight - borderCalc) {
                player.cells[i].y = c.gameHeight - borderCalc;
            }
            if (player.cells[i].x < borderCalc) {
                player.cells[i].x = borderCalc;
            }
            if (player.cells[i].y < borderCalc) {
                player.cells[i].y = borderCalc;
            }
            x += player.cells[i].x;
            y += player.cells[i].y;
        }
    }

    // 1.8. Player position is the average position of all player-cells
    player.x = x/player.cells.length;
    player.y = y/player.cells.length;
}

/**
 * Move a mass
 * @param {a mass to move} mass 
 */
function moveMass(mass) {
    var deg = Math.atan2(mass.target.y, mass.target.x);
    var deltaY = mass.speed * Math.sin(deg);
    var deltaX = mass.speed * Math.cos(deg);

    mass.speed -= 0.5;
    if(mass.speed < 0) {
        mass.speed = 0;
    }
    if (!isNaN(deltaY)) {
        mass.y += deltaY;
    }
    if (!isNaN(deltaX)) {
        mass.x += deltaX;
    }

    var borderCalc = mass.radius + 5;

    if (mass.x > c.gameWidth - borderCalc) {
        mass.x = c.gameWidth - borderCalc;
    }
    if (mass.y > c.gameHeight - borderCalc) {
        mass.y = c.gameHeight - borderCalc;
    }
    if (mass.x < borderCalc) {
        mass.x = borderCalc;
    }
    if (mass.y < borderCalc) {
        mass.y = borderCalc;
    }
}

/**
 * Balance total mass in game 
 * Consider to remove or add more food
 */
function balanceMass() {
    var totalMass = food.length * c.foodMass +
        users
            .map(function(u) {return u.massTotal; })
            .reduce(function(pu,cu) { return pu+cu;}, 0);

    var massDiff = c.gameMass - totalMass;
    var maxFoodDiff = c.maxFood - food.length;
    var foodDiff = parseInt(massDiff / c.foodMass) - maxFoodDiff;
    var foodToAdd = Math.min(foodDiff, maxFoodDiff);
    var foodToRemove = -Math.max(foodDiff, maxFoodDiff);


    if (foodToAdd > 0) {
        //console.log('[DEBUG] Adding ' + foodToAdd + ' food to level!');
        addFood(foodToAdd);
        //console.log('[DEBUG] Mass rebalanced!');
    }
    else if (foodToRemove > 0) {
        //console.log('[DEBUG] Removing ' + foodToRemove + ' food from level!');
        removeFood(foodToRemove);
        //console.log('[DEBUG] Mass rebalanced!');
    }

    var virusToAdd = c.maxVirus - virus.length;

    if (virusToAdd > 0) {
        addVirus(virusToAdd);
    }
}

io.on('connection', function (socket) {
    console.log('A user connected!', socket.handshake.query.type);

    // 1. Initialize player when new socket-connect
    // --> Can update this logic in-future - check this socket is a reconnect or not
    // --> Handle 2 cases: new-connect or reconnect
    // 1.1 Player-type
    var type = socket.handshake.query.type;
    // 1.2 Player init-radius
    var radius = util.massToRadius(c.defaultPlayerMass);
    // 1.3 Player random init-position
    var position = c.newPlayerInitialPosition == 'farthest' ? util.uniformPosition(users, radius) : util.randomPosition(radius);
    // 1.4 Player cell-list
    var cells = [];
    var massTotal = 0;
    if(type === 'player') {
        // A cell of player
        cells = [{
            // cell.1. mass
            mass: c.defaultPlayerMass,
            // cell.2. position
            x: position.x,
            y: position.y,
            // cell.3. radius
            radius: radius
        }];
        // Total mass: total mass of player's cells
        massTotal = c.defaultPlayerMass;
    }

    // 1.5 Player attribute
    var currentPlayer = {
        // player.1. id = socket.id
        id: socket.id,
        // player.2. postion 
        x: position.x,
        y: position.y,
        // player.3. (width,height) of player
        w: c.defaultPlayerMass,
        h: c.defaultPlayerMass,
        // player.5. cell-list of player 
        cells: cells,
        // player.6. total-mass of player
        massTotal: massTotal,
        // player.7. color of player 
        hue: Math.round(Math.random() * 360),
        // player.8. type of player 
        type: type,
        // player.9. last-heart-beat-timestamp of player
        lastHeartbeat: new Date().getTime(),
        // player.10. moving-target of player
        target: {
            x: 0,
            y: 0
        }
    };


    // Connect.2. 'Gotit' - client reply - got player-data from server
    // Client send client-player-data to server
    socket.on('gotit', function (player) {
        console.log('[INFO] Player ' + player.name + ' connecting!');

        
        if (util.findIndex(users, player.id) > -1) {
            // Gotit.1. Check player alredy connected or not 
            console.log('[INFO] Player ID is already connected, kicking.');
            socket.disconnect();
        } else if (!util.validNick(player.name)) {
            // Gotit.2. Check player-name valid or not
            socket.emit('kick', 'Invalid username.');
            socket.disconnect();
        } else {
            // Gotit.3. Player-valid - join player to game-room
            // Now there is only 1 global game-room
            // In-future can create multiple rooms: lobby-room, game-rooms, many game-type
            console.log('[INFO] Player ' + player.name + ' connected!');

            // 1. Assign socket
            sockets[player.id] = socket;
            // 2. Assign radius
            var radius = util.massToRadius(c.defaultPlayerMass);
            // 3. Assign position 
            var position = c.newPlayerInitialPosition == 'farthest' ? 
                util.uniformPosition(users, radius) 
                : util.randomPosition(radius);
            player.x = position.x;
            player.y = position.y;
            // 4. Assign target
            player.target.x = 0;
            player.target.y = 0;
            // 5. Player-type: play or view
            if(type === 'player') {
                player.cells = [{
                    mass: c.defaultPlayerMass,
                    x: position.x,
                    y: position.y,
                    radius: radius
                }];
                player.massTotal = c.defaultPlayerMass;
            }
            else {
                 player.cells = [];
                 player.massTotal = 0;
            }
            // 6. Player-color
            player.hue = Math.round(Math.random() * 360);
            
            // 7. Assign currentPlayer of this socket to new player-data: combine with client-data
            currentPlayer = player;
            // 7. Assign last-heart-beat
            currentPlayer.lastHeartbeat = new Date().getTime();
            // 7. Append currentPlayer to player-list
            users.push(currentPlayer);
            // 8. IO broadcast 'PlayerJoin' to ALL player in Game-room
            io.emit('playerJoin', { name: currentPlayer.name });
            // 9. Socket send to client 'GameSetup' wit game-size
            socket.emit('gameSetup', {
                gameWidth: c.gameWidth,
                gameHeight: c.gameHeight
            });
            console.log('Total players: ' + users.length);
        }

    });

    socket.on('pingcheck', function () {
        socket.emit('pongcheck');
    });

    socket.on('windowResized', function (data) {
        currentPlayer.screenWidth = data.screenWidth;
        currentPlayer.screenHeight = data.screenHeight;
    });

    // Connect.1. Respawn is the starting step - first event from client
    socket.on('respawn', function () {
        // Respawn.1. Remove player if exist in player-list before
        if (util.findIndex(users, currentPlayer.id) > -1)
            users.splice(util.findIndex(users, currentPlayer.id), 1);
        // Respawn.2. Send 'Welcome' event from server 
        // - with player-data initialized from server
        socket.emit('welcome', currentPlayer);
        console.log('[INFO] User ' + currentPlayer.name + ' respawned!');
    });

    socket.on('disconnect', function () {
        if (util.findIndex(users, currentPlayer.id) > -1)
            users.splice(util.findIndex(users, currentPlayer.id), 1);
        console.log('[INFO] User ' + currentPlayer.name + ' disconnected!');

        socket.broadcast.emit('playerDisconnect', { name: currentPlayer.name });
    });

    socket.on('playerChat', function(data) {
        var _sender = data.sender.replace(/(<([^>]+)>)/ig, '');
        var _message = data.message.replace(/(<([^>]+)>)/ig, '');
        if (c.logChat === 1) {
            console.log('[CHAT] [' + (new Date()).getHours() + ':' + (new Date()).getMinutes() + '] ' + _sender + ': ' + _message);
        }
        socket.broadcast.emit('serverSendPlayerChat', {sender: _sender, message: _message.substring(0,35)});
    });

    socket.on('pass', function(data) {
        if (data[0] === c.adminPass) {
            console.log('[ADMIN] ' + currentPlayer.name + ' just logged in as an admin!');
            socket.emit('serverMSG', 'Welcome back ' + currentPlayer.name);
            socket.broadcast.emit('serverMSG', currentPlayer.name + ' just logged in as admin!');
            currentPlayer.admin = true;
        } else {
            
            // TODO: Actually log incorrect passwords.
              console.log('[ADMIN] ' + currentPlayer.name + ' attempted to log in with incorrect password.');
              socket.emit('serverMSG', 'Password incorrect, attempt logged.');
             pool.query('INSERT INTO logging SET name=' + currentPlayer.name + ', reason="Invalid login attempt as admin"');
        }
    });

    socket.on('kick', function(data) {
        if (currentPlayer.admin) {
            var reason = '';
            var worked = false;
            for (var e = 0; e < users.length; e++) {
                if (users[e].name === data[0] && !users[e].admin && !worked) {
                    if (data.length > 1) {
                        for (var f = 1; f < data.length; f++) {
                            if (f === data.length) {
                                reason = reason + data[f];
                            }
                            else {
                                reason = reason + data[f] + ' ';
                            }
                        }
                    }
                    if (reason !== '') {
                       console.log('[ADMIN] User ' + users[e].name + ' kicked successfully by ' + currentPlayer.name + ' for reason ' + reason);
                    }
                    else {
                       console.log('[ADMIN] User ' + users[e].name + ' kicked successfully by ' + currentPlayer.name);
                    }
                    socket.emit('serverMSG', 'User ' + users[e].name + ' was kicked by ' + currentPlayer.name);
                    sockets[users[e].id].emit('kick', reason);
                    sockets[users[e].id].disconnect();
                    users.splice(e, 1);
                    worked = true;
                }
            }
            if (!worked) {
                socket.emit('serverMSG', 'Could not locate user or user is an admin.');
            }
        } else {
            console.log('[ADMIN] ' + currentPlayer.name + ' is trying to use -kick but isn\'t an admin.');
            socket.emit('serverMSG', 'You are not permitted to use this command.');
        }
    });

    // Heartbeat function, update everytime.
    socket.on('0', function(target) {
        currentPlayer.lastHeartbeat = new Date().getTime();
        if (target.x !== currentPlayer.x || target.y !== currentPlayer.y) {
            currentPlayer.target = target;
        }
    });

    socket.on('1', function() {
        // Fire food.
        for(var i=0; i<currentPlayer.cells.length; i++)
        {
            if(((currentPlayer.cells[i].mass >= c.defaultPlayerMass + c.fireFood) && c.fireFood > 0) || (currentPlayer.cells[i].mass >= 20 && c.fireFood === 0)){
                var masa = 1;
                if(c.fireFood > 0)
                    masa = c.fireFood;
                else
                    masa = currentPlayer.cells[i].mass*0.1;
                currentPlayer.cells[i].mass -= masa;
                currentPlayer.massTotal -=masa;
                massFood.push({
                    id: currentPlayer.id,
                    num: i,
                    masa: masa,
                    hue: currentPlayer.hue,
                    target: {
                        x: currentPlayer.x - currentPlayer.cells[i].x + currentPlayer.target.x,
                        y: currentPlayer.y - currentPlayer.cells[i].y + currentPlayer.target.y
                    },
                    x: currentPlayer.cells[i].x,
                    y: currentPlayer.cells[i].y,
                    radius: util.massToRadius(masa),
                    speed: 25
                });
            }
        }
    });
    socket.on('2', function(virusCell) {
        function splitCell(cell) {
            if(cell && cell.mass && cell.mass >= c.defaultPlayerMass*2) {
                cell.mass = cell.mass/2;
                cell.radius = util.massToRadius(cell.mass);
                currentPlayer.cells.push({
                    mass: cell.mass,
                    x: cell.x,
                    y: cell.y,
                    radius: cell.radius,
                    speed: 25
                });
            }
        }

        if(currentPlayer.cells.length < c.limitSplit && currentPlayer.massTotal >= c.defaultPlayerMass*2) {
            //Split single cell from virus
            if(virusCell) {
              splitCell(currentPlayer.cells[virusCell]);
            }
            else {
              //Split all cells
              if(currentPlayer.cells.length < c.limitSplit && currentPlayer.massTotal >= c.defaultPlayerMass*2) {
                  var numMax = currentPlayer.cells.length;
                  for(var d=0; d<numMax; d++) {
                      splitCell(currentPlayer.cells[d]);
                  }
              }
            }
            currentPlayer.lastSplit = new Date().getTime();
        }
    });
});

/**
 * Check all game-logic-condition for this player
 * @param {the player to tick} currentPlayer 
 */
function tickPlayer(currentPlayer) {
    /*
    1. Kick timeout player
    In-future can change to new logic
    - Server: AFK-player - stay-idle
    - Client: connection problem - try to reconnect
    - Server: accept reconnect - renew-socket - update new state 
    - Client: update newstate - continue playing
    */
    if(currentPlayer.lastHeartbeat < new Date().getTime() - c.maxHeartbeatInterval) {
        sockets[currentPlayer.id].emit('kick', 'Last heartbeat received over ' + c.maxHeartbeatInterval + ' ago.');
        sockets[currentPlayer.id].disconnect();
    }

    // 2. Move player 
    movePlayer(currentPlayer);

    // Util.1. Check point in circle 
    // --> Check player eat food success or not
    // Consider food is a point with unit-size
    function funcFood(f) {
        return SAT.pointInCircle(new V(f.x, f.y), playerCircle);
    }

    // Util.2. Delete food at position f
    function deleteFood(f) {
        food[f] = {};
        food.splice(f, 1);
    }

    // Util.3. Check circle in circle by check center in circle 
    // --> Check player eat other mass
    function eatMass(m) {
        if(SAT.pointInCircle(new V(m.x, m.y), playerCircle)){
            // If this mass belong to player and still moving with player
            if(m.id == currentPlayer.id && m.speed > 0 && z == m.num)
                return false;
            // Else this mass is free to eat and can be eat by check mass
            if(currentCell.mass > m.mass * 1.1)
                return true;
        }
        return false;
    }

    // Util.3. Check ?
    function check(user) {
        for(var i=0; i<user.cells.length; i++) {
            if(user.cells[i].mass > 10 && user.id !== currentPlayer.id) {
                var response = new SAT.Response();
                var collided = SAT.testCircleCircle(
                    playerCircle,
                    new C(
                        new V(user.cells[i].x, user.cells[i].y), 
                        user.cells[i].radius
                        ),
                    response
                    );
                if (collided) {
                    response.aUser = currentCell;
                    response.bUser = {
                        id: user.id,
                        name: user.name,
                        x: user.cells[i].x,
                        y: user.cells[i].y,
                        num: i,
                        mass: user.cells[i].mass
                    };
                    playerCollisions.push(response);
                }
            }
        }
        return true;
    }

    /**
     * 
     * @param {*} collision 
     */
    function collisionCheck(collision) {
        if (collision.aUser.mass > collision.bUser.mass * 1.1  && collision.aUser.radius > Math.sqrt(Math.pow(collision.aUser.x - collision.bUser.x, 2) + Math.pow(collision.aUser.y - collision.bUser.y, 2))*1.75) {
            console.log('[DEBUG] Killing user: ' + collision.bUser.id);
            console.log('[DEBUG] Collision info:');
            console.log(collision);

            var numUser = util.findIndex(users, collision.bUser.id);
            if (numUser > -1) {
                if(users[numUser].cells.length > 1) {
                    users[numUser].massTotal -= collision.bUser.mass;
                    users[numUser].cells.splice(collision.bUser.num, 1);
                } else {
                    users.splice(numUser, 1);
                    io.emit('playerDied', { name: collision.bUser.name });
                    sockets[collision.bUser.id].emit('RIP');
                }
            }
            currentPlayer.massTotal += collision.bUser.mass;
            collision.aUser.mass += collision.bUser.mass;
        }
    }


    for(var z=0; z<currentPlayer.cells.length; z++) {
        var currentCell = currentPlayer.cells[z];
        var playerCircle = new C(
            new V(currentCell.x, currentCell.y),
            currentCell.radius
        );

        var foodEaten = food.map(funcFood)
            .reduce( function(a, b, c) { return b ? a.concat(c) : a; }, []);

        foodEaten.forEach(deleteFood);

        var massEaten = massFood.map(eatMass)
            .reduce(function(a, b, c) {return b ? a.concat(c) : a; }, []);

        var virusCollision = virus.map(funcFood)
           .reduce( function(a, b, c) { return b ? a.concat(c) : a; }, []);

        if(virusCollision > 0 && currentCell.mass > virus[virusCollision].mass) {
          sockets[currentPlayer.id].emit('virusSplit', z);
          virus.splice(virusCollision, 1);
        }

        var masaGanada = 0;
        for(var m=0; m<massEaten.length; m++) {
            masaGanada += massFood[massEaten[m]].masa;
            massFood[massEaten[m]] = {};
            massFood.splice(massEaten[m],1);
            for(var n=0; n<massEaten.length; n++) {
                if(massEaten[m] < massEaten[n]) {
                    massEaten[n]--;
                }
            }
        }

        if(typeof(currentCell.speed) == "undefined")
            currentCell.speed = 6.25;
        masaGanada += (foodEaten.length * c.foodMass);
        currentCell.mass += masaGanada;
        currentPlayer.massTotal += masaGanada;
        currentCell.radius = util.massToRadius(currentCell.mass);
        playerCircle.r = currentCell.radius;

        tree.clear();
        users.forEach(tree.put);
        var playerCollisions = [];

        var otherUsers =  tree.get(currentPlayer, check);

        playerCollisions.forEach(collisionCheck);
    }
}

// Loop.1. Move-loop: make the game-object moving as movement-parameters
function moveloop() {
    // 1. Tick all player - because only player moving - tick other if we make other object move 
    for (var i = 0; i < users.length; i++) {
        tickPlayer(users[i]);
    }
    // 2. Mass-food: the mass-food coming out from player - move them if they are still moving
    for (i=0; i < massFood.length; i++) {
        if(massFood[i].speed > 0) {
            moveMass(massFood[i]);
        }
    }
}

// Loop.2. Game-loop: 
function gameloop() {
    if (users.length > 0) {
        // 1. Build leaderboard
        // 1.1. Sort user by massTotal
        users.sort( function(a, b) { return b.massTotal - a.massTotal; });
        // 1.2. Build top-user by massTotal
        var topUsers = [];

        for (var i = 0; i < Math.min(10, users.length); i++) {
            if(users[i].type == 'player') {
                topUsers.push({
                    id: users[i].id,
                    name: users[i].name
                });
            }
        }
        // 1.3. Check leaderboard is changed or not AND update leaderboard
        if (isNaN(leaderboard) || leaderboard.length !== topUsers.length) {
            leaderboard = topUsers;
            leaderboardChanged = true;
        }
        else {
            for (i = 0; i < leaderboard.length; i++) {
                if (leaderboard[i].id !== topUsers[i].id) {
                    leaderboard = topUsers;
                    leaderboardChanged = true;
                    break;
                }
            }
        }

        // 2. Make user lose mass
        for (i = 0; i < users.length; i++) {
            for(var z=0; z < users[i].cells.length; z++) {
                if (users[i].cells[z].mass * (1 - (c.massLossRate / 1000)) > c.defaultPlayerMass && users[i].massTotal > c.minMassLoss) {
                    var massLoss = users[i].cells[z].mass * (1 - (c.massLossRate / 1000));
                    users[i].massTotal -= users[i].cells[z].mass - massLoss;
                    users[i].cells[z].mass = massLoss;
                }
            }
        }
    }

    // 3. Balance mass in game
    balanceMass();
}

// Loop.3. Network-loop
function sendUpdates() {
    // Send update for each user
    users.forEach( function(u) {
        // 1. Check the position of the playing-view - focus around player-position
        // If this is spectator --> then focus on the center of the game-map
        // center the view if x/y is undefined, this will happen for spectators
        u.x = u.x || c.gameWidth / 2;
        u.y = u.y || c.gameHeight / 2;

        // 2. Check if this game-object should send update to the client or not 
        // --> Send-update iff game-object in the player-view

        // 2.1. Visible-food
        var visibleFood  = food
            .map(function(f) {
                if ( f.x > u.x - u.screenWidth/2 - 20 &&
                    f.x < u.x + u.screenWidth/2 + 20 &&
                    f.y > u.y - u.screenHeight/2 - 20 &&
                    f.y < u.y + u.screenHeight/2 + 20) {
                    return f;
                }
            })
            .filter(function(f) { return f; });

        // 2.2. Visible-virus    
        var visibleVirus  = virus
            .map(function(f) {
                if ( f.x > u.x - u.screenWidth/2 - f.radius &&
                    f.x < u.x + u.screenWidth/2 + f.radius &&
                    f.y > u.y - u.screenHeight/2 - f.radius &&
                    f.y < u.y + u.screenHeight/2 + f.radius) {
                    return f;
                }
            })
            .filter(function(f) { return f; });
        
        // 2.3. Visible-food
        var visibleMass = massFood
            .map(function(f) {
                if ( f.x+f.radius > u.x - u.screenWidth/2 - 20 &&
                    f.x-f.radius < u.x + u.screenWidth/2 + 20 &&
                    f.y+f.radius > u.y - u.screenHeight/2 - 20 &&
                    f.y-f.radius < u.y + u.screenHeight/2 + 20) {
                    return f;
                }
            })
            .filter(function(f) { return f; });

        // 2.4. Visible-cells - other player
        var visibleCells  = users
            .map(function(f) {
                for(var z=0; z<f.cells.length; z++)
                {
                    if ( f.cells[z].x+f.cells[z].radius > u.x - u.screenWidth/2 - 20 &&
                        f.cells[z].x-f.cells[z].radius < u.x + u.screenWidth/2 + 20 &&
                        f.cells[z].y+f.cells[z].radius > u.y - u.screenHeight/2 - 20 &&
                        f.cells[z].y-f.cells[z].radius < u.y + u.screenHeight/2 + 20) {
                        z = f.cells.lenth;
                        if(f.id !== u.id) {
                            return {
                                id: f.id,
                                x: f.x,
                                y: f.y,
                                cells: f.cells,
                                massTotal: Math.round(f.massTotal),
                                hue: f.hue,
                                name: f.name
                            };
                        } else {
                            //console.log("Nombre: " + f.name + " Es Usuario");
                            // Return only needed data of the cells - remove other server-logic data
                            return {
                                x: f.x,
                                y: f.y,
                                cells: f.cells,
                                massTotal: Math.round(f.massTotal),
                                hue: f.hue,
                            };
                        }
                    }
                }
            })
            .filter(function(f) { return f; });

        // 3. Socket emit event 'serverTellPlayerMove' with data to update
        // visible-Cells
        // visible-Food
        // visible-Mass
        // visible-Virus
        sockets[u.id].emit('serverTellPlayerMove', visibleCells, visibleFood, visibleMass, visibleVirus);
        // 3.1. If leaderboard-changed - then emit 'leaderboard' with leaderboard-data
        if (leaderboardChanged) {
            sockets[u.id].emit('leaderboard', {
                players: users.length,
                leaderboard: leaderboard
            });
        }
    });

    leaderboardChanged = false;
}

// Connect.4. Start the main-logic-loop
// Loop.1. Physic-movement-loop
setInterval(moveloop, 1000 / 60);
// Loop.2. Game-logic-loop
setInterval(gameloop, 1000);
// Loop.3. Network-update-loop
setInterval(sendUpdates, 1000 / c.networkUpdateFactor);

// Don't touch, IP configurations.
var ipaddress = process.env.OPENSHIFT_NODEJS_IP || process.env.IP || c.host;
var serverport = process.env.OPENSHIFT_NODEJS_PORT || process.env.PORT || c.port;
http.listen( serverport, ipaddress, function() {
    console.log('[DEBUG] Listening on ' + ipaddress + ':' + serverport);
});
