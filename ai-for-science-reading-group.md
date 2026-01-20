---
layout: landing
title: AI for Science Reading Group
permalink: /ai-for-science-reading-group/
slack_invite: http://ai-for-science-sf.slack.com/
signup_form: https://docs.google.com/spreadsheets/d/1l1CQtxwq7mSs1Zdt0TiZWXl-MyegZVNZa028RaSKADA/edit?usp=sharing
notes_doc: https://example.com/ai4s-notes
drive_link: https://example.com/ai4s-archive
meeting_day_time: "Sundays · 3:00–4:30pm"
meeting_location: "San Francisco (in-person)"
next_session:
  date: "February 1, 2026"
  time: "3:00–4:30pm PT"
  title: "rbio1 — training scientific reasoning LLMs with biological world models as soft verifiers"
  presenter: "TBD — volunteer!"
  paper_title: "rbio1 — training scientific reasoning LLMs with biological world models as soft verifiers"
  paper_link: https://www.biorxiv.org/content/10.1101/2025.08.18.670981v3.full.pdf
  location: "San Francisco (in-person)"
  abstract: "How to pair large language models with biological world models that act as soft verifiers for scientific reasoning tasks, plus a walkthrough of the training setup."
  deck_link: https://example.com/next-deck
  notes_link: https://example.com/next-notes
past_sessions: []
resources:
  - label: "Slack workspace"
    href: http://ai-for-science-sf.slack.com/
    description: "Day-to-day coordination, quick paper polls, and reminders."
  - label: "Slides & notes archive"
    href: https://example.com/ai4s-archive
    description: "Decks and shared notes from sessions."
  - label: "Running notes"
    href: https://example.com/ai4s-notes
    description: "Living document of discussion summaries and open questions."
---

<div class="ai4s-page">
  <div class="ai4s-shell">
<div class="ai4s-portal">
  <div class="ai4s-hero" id="top">
    <h1>{{ page.title }}</h1>
    <p class="ai4s-hero__lead">
      Application-focused reading group where we dissect state-of-the-art methods seeking to accelerate the process of scientific discovery.
    </p>
    <div class="ai4s-inline-nav">
      <a href="#next-session">Next session</a>
      <a href="#past-sessions">Past sessions</a>
      <a href="#resources">Resources</a>
    </div>
    <div class="ai4s-hero__chips">
      <span class="ai4s-chip">{{ page.meeting_day_time }}</span>
      <span class="ai4s-chip">{{ page.meeting_location }}</span>
    </div>
    <div class="ai4s-hero__actions">
      <a class="ai4s-button primary" href="{{ page.slack_invite }}">Join the Slack</a>
      <a class="ai4s-button text" href="{{ page.signup_form }}">Propose a paper</a>
    </div>
  </div>

  <div class="ai4s-section" id="next-session">
    <div class="ai4s-section__header">
      <div>
        <p class="ai4s-eyebrow">Up next</p>
        <h2>Next session</h2>
      </div>
    </div>
    <div class="ai4s-next-card">
      <div class="ai4s-next-card__header">
        <span class="ai4s-pill solid">Weekly</span>
        <span class="ai4s-next-date">{{ page.next_session.date }} · {{ page.next_session.time }}</span>
      </div>
      <h3 class="ai4s-next-title">{{ page.next_session.title }}</h3>
      <p class="ai4s-next-meta">
        <strong>{{ page.next_session.presenter }}</strong>
        {% if page.next_session.paper_link %}
          · <a class="ai4s-text-link" href="{{ page.next_session.paper_link }}">{{ page.next_session.paper_title }}</a>
        {% else %}
          · {{ page.next_session.paper_title }}
        {% endif %}
      </p>
      <p class="ai4s-next-abstract">{{ page.next_session.abstract }}</p>
      <div class="ai4s-detail-grid">
        <div class="ai4s-detail">
          <span class="ai4s-detail-label">Location</span>
          <span class="ai4s-detail-value">{{ page.next_session.location }}</span>
        </div>
        <div class="ai4s-detail">
          <span class="ai4s-detail-label">Flow</span>
          <span class="ai4s-detail-value">30 min walkthrough · 30 min discussion · wrap-up</span>
        </div>
      </div>
      <div class="ai4s-session-links">
        {% if page.next_session.paper_link %}
          <a class="ai4s-tag" href="{{ page.next_session.paper_link }}">Paper</a>
        {% endif %}
        {% if page.next_session.deck_link %}
          <a class="ai4s-tag" href="{{ page.next_session.deck_link }}">Deck</a>
        {% endif %}
        {% if page.next_session.notes_link %}
          <a class="ai4s-tag" href="{{ page.next_session.notes_link }}">Notes</a>
        {% endif %}
      </div>
    </div>
  </div>

  <div class="ai4s-section" id="past-sessions">
    <div class="ai4s-section__header">
      <div>
        <p class="ai4s-eyebrow">Session archive</p>
        <h2>Recent sessions</h2>
      </div>
      <a class="ai4s-text-link" href="{{ page.drive_link }}">Browse the archive</a>
    </div>
    <div class="ai4s-session-grid">
      {% if page.past_sessions and page.past_sessions.size > 0 %}
        {% for session in page.past_sessions %}
          <article class="ai4s-card ai4s-session-card">
            <div class="ai4s-session-date">{{ session.date }}</div>
            <h3 class="ai4s-session-title">{{ session.title }}</h3>
            <p class="ai4s-session-meta">
              {{ session.presenter }}
              {% if session.paper_link %}
                · <a class="ai4s-text-link" href="{{ session.paper_link }}">Paper</a>
              {% endif %}
            </p>
            {% if session.takeaway %}
              <p class="ai4s-session-note">{{ session.takeaway }}</p>
            {% endif %}
            <div class="ai4s-session-links">
              {% if session.deck_link %}
                <a class="ai4s-tag" href="{{ session.deck_link }}">Slides</a>
              {% endif %}
              {% if session.recording_link %}
                <a class="ai4s-tag" href="{{ session.recording_link }}">Recording</a>
              {% endif %}
            </div>
          </article>
        {% endfor %}
      {% else %}
        <article class="ai4s-card ai4s-session-card ai4s-session-empty">
          <div class="ai4s-session-date">Coming soon</div>
          <h3 class="ai4s-session-title">We’ll post materials after our first session</h3>
          <p class="ai4s-session-note">Check back here once we’ve met. In the meantime, grab details above or propose a paper.</p>
        </article>
      {% endif %}
    </div>
  </div>

  <div class="ai4s-section ai4s-secondary" id="resources">
    <div class="ai4s-section__header">
      <div>
        <p class="ai4s-eyebrow">Stay connected</p>
        <h2>Resources</h2>
      </div>
      <a class="ai4s-text-link" href="{{ page.slack_invite }}">Ping us on Slack</a>
    </div>
    <div class="ai4s-resource-grid">
      {% for resource in page.resources %}
        <a class="ai4s-card ai4s-resource" href="{{ resource.href }}">
          <h3 class="ai4s-resource-title">
            <span class="ai4s-resource-icon">
              {% case resource.label %}
                {% when "Slack workspace" %}
                  <i class="fa-brands fa-slack"></i>
                {% when "Slides & notes archive" %}
                  <i class="fa-solid fa-clapperboard"></i>
                {% when "Running notes" %}
                  <i class="fa-solid fa-note-sticky"></i>
                {% else %}
                  <i class="fa-solid fa-circle"></i>
              {% endcase %}
            </span>
            {{ resource.label }}
          </h3>
          <p class="ai4s-resource-text">{{ resource.description }}</p>
        </a>
      {% endfor %}
    </div>
  </div>

  <div class="ai4s-section" id="sponsorship">
    <div class="ai4s-section__header">
      <div>
        <p class="ai4s-eyebrow">Support</p>
        <h2>Sponsorship</h2>
      </div>
    </div>
    <p>
      If you’d like to support snacks, space, or speakers, reach out to
      <a href="mailto:ypatel5400@gmail.com">ypatel5400@gmail.com</a>.
    </p>
  </div>

  <div class="ai4s-section" id="organizers">
    <div class="ai4s-section__header">
      <div>
        <p class="ai4s-eyebrow">Organizers</p>
        <h2>Reach us</h2>
      </div>
    </div>
    <div class="ai4s-reading-grid">
      <article class="ai4s-card ai4s-paper">
        <h3 class="ai4s-paper-title"><a href="https://ypatel.io">Yash Patel</a></h3>
        <p class="ai4s-paper-note">Research Engineer @ <a href="https://harmonic.fun">Harmonic</a>.</p>
      </article>
      <article class="ai4s-card ai4s-paper">
        <h3 class="ai4s-paper-title"><a href="https://www.linkedin.com/in/alexbeatson/">Alex Beatson</a></h3>
        <p class="ai4s-paper-note">Co-Founder of <a href="https://www.axi.om/">Axiom Bio</a>.</p>
      </article>
    </div>
  </div>
</div>
  </div>
</div>
