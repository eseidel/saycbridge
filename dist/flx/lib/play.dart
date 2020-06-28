import 'package:flutter/material.dart' hide Card;
import 'package:flutter/material.dart' as material show Card;
import 'package:saycbridge/model.dart';

class PlayHome extends StatefulWidget {
  PlayHomeState createState() => PlayHomeState();
}

class PlayHomeState extends State<PlayHome> {
  Deal deal;

  @override
  void initState() {
    reDeal();
    super.initState();
  }

  void reDeal() {
    setState(() {
      deal = Deal.random();
    });
  }

  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        title: Text('Play'),
      ),
      body: Material(
        child: PlayTable(this.deal),
      ),
      floatingActionButton: FloatingActionButton(
        child: Icon(Icons.refresh),
        onPressed: reDeal,
      ),
    );
  }
}

class SuitLine extends StatelessWidget {
  final Hand hand;
  final Suit suit;
  SuitLine(this.hand, this.suit);

  Widget build(BuildContext context) {
    List<Card> cards = hand.matchingSuit(suit).toList();
    // Flip the sort to put spades on top.
    cards.sort((a, b) => -a.rank.index.compareTo(b.rank.index));
    String cardsString = cards.map((card) => card.rank.name).join(" ");
    return Row(
      children: [
        Text(suit.codePoint),
        Text(cardsString),
      ],
    );
  }
}

class HandSummary extends StatelessWidget {
  final Position position;
  final Hand hand;
  HandSummary(this.position, this.hand);

  Widget build(BuildContext context) {
    List<Suit> displayOrder = [
      Suit.spades,
      Suit.hearts,
      Suit.diamonds,
      Suit.clubs
    ];
    return material.Card(
      margin: EdgeInsets.all(10),
      child: Padding(
        padding: const EdgeInsets.all(8.0),
        child: SizedBox(
          width: 100, // HACK?
          child: Column(
            crossAxisAlignment: CrossAxisAlignment.start,
            children: [
              new Text(position.name),
              for (Suit suit in displayOrder) SuitLine(hand, suit),
            ],
          ),
        ),
      ),
    );
  }
}

class DealSummary extends StatelessWidget {
  final Deal deal;
  DealSummary(this.deal);

  HandSummary _hand(Position position) =>
      HandSummary(position, deal.handFor(position));

  Widget build(BuildContext context) {
    return Row(
      mainAxisAlignment: MainAxisAlignment.center,
      children: [
        _hand(Position.west),
        Column(
          children: [_hand(Position.north), _hand(Position.south)],
        ),
        _hand(Position.east),
      ],
    );
  }
}

List<Card> sortForDisplay(List<Card> unsorted) {
  // Alternating colors for now:
  List<Suit> suitOrder = [Suit.spades, Suit.hearts, Suit.clubs, Suit.diamonds];
  // Should eventually handle missing suits, trump, etc.
  List<Card> sorted = List.from(unsorted); // Is this copy needed?
  sorted.sort((a, b) {
    if (a.suit != b.suit)
      return suitOrder.indexOf(a.suit).compareTo(suitOrder.indexOf(b.suit));
    return -a.rank.index.compareTo(b.rank.index);
  });
  return sorted;
}

typedef void CardSelectCallback(Card which);

class CardSpread extends StatelessWidget {
  final Hand hand;
  final CardSelectCallback selectCard;
  final Card selectedCard;

  CardSpread(this.hand, this.selectCard, {this.selectedCard});

  Widget _card(Card card) {
    return GestureDetector(
      onTapDown: (_) => selectCard(card),
      child: Container(
        decoration: BoxDecoration(
          border: Border(
            top: BorderSide(),
            left: BorderSide(),
          ),
          color: (card == selectedCard) ? Colors.red : null,
        ),
        padding: EdgeInsets.all(5),
        child: Column(
          children: [Text(card.rank.displayRank), Text(card.suit.codePoint)],
        ),
      ),
    );
  }

  Widget build(BuildContext context) {
    List<Card> sorted = sortForDisplay(hand.cards);
    return Row(
      mainAxisSize: MainAxisSize.min,
      children: [for (Card card in sorted) _card(card)],
    );
  }
}

class PlayControls extends StatefulWidget {
  final Hand hand;
  final Position position;
  final String playerName;

  PlayControls(this.hand, this.position, this.playerName);

  @override
  _PlayControlsState createState() => _PlayControlsState();
}

class _PlayControlsState extends State<PlayControls> {
  Card selected;

  Widget build(BuildContext context) {
    return Column(
      children: [
        CardSpread(widget.hand, (Card card) {
          setState(() {
            selected = card;
          });
        }, selectedCard: selected),
        Container(
          decoration: BoxDecoration(border: Border.all()),
          child: Row(
            children: [Text(widget.position.name), Text(widget.playerName)],
          ),
        ),
      ],
    );
  }
}

class CurrentTrick extends StatelessWidget {
  Widget build(BuildContext context) {
    return SizedBox(width: 200, height: 200);
  }
}

class PlayTable extends StatelessWidget {
  final Deal deal;
  final Position player = Position.south;

  PlayTable(this.deal);

  PlayControls _hand(Position position) => PlayControls(
      deal.handFor(position), position, position == player ? "You" : "");

  Widget build(BuildContext context) {
    return Center(
      child: Column(children: [
        Text("Contract: 1S"),
        Row(
          mainAxisAlignment: MainAxisAlignment.center,
          children: [
            _hand(Position.west),
            Column(
              children: [
                _hand(Position.north),
                CurrentTrick(),
                _hand(Position.south),
              ],
            ),
            _hand(Position.east),
          ],
        ),
      ]),
    );
  }
}
