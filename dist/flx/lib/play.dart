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
    return a.rank.index.compareTo(b.rank.index);
  });
  return sorted;
}

typedef void CardSelectCallback(Card which);

class CardSpread extends StatelessWidget {
  final Hand hand;
  final CardSelectCallback selectCard;

  CardSpread(this.hand, this.selectCard);

  Widget _card(Card card) {
    return Container(
      decoration: BoxDecoration(
        border: Border(top: BorderSide(), left: BorderSide()),
      ),
      padding: EdgeInsets.all(5),
      child: Column(
        children: [Text(card.rank.displayRank), Text(card.suit.codePoint)],
      ),
    );
  }

  Widget build(BuildContext context) {
    List<Card> sorted = sortForDisplay(hand.cards);
    return Row(children: [for (Card card in sorted) _card(card)]);
  }
}

class PlayControls extends StatelessWidget {
  final Hand hand;
  final Position position;
  final String playerName = 'You';

  PlayControls(this.hand, this.position);

  Widget build(BuildContext context) {
    return Column(
      children: [
        CardSpread(hand, (_) {}),
        Row(
          children: [Text(position.name), Text(playerName)],
        ),
      ],
    );
  }
}

class PlayTable extends StatelessWidget {
  final Deal deal;
  final Position player = Position.south;

  PlayTable(this.deal);

  Widget build(BuildContext context) {
    return Column(children: [
      Text("Contract: 1S"),
      DealSummary(deal),
      PlayControls(deal.handFor(player), player),
    ]);
  }
}
