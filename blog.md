---
layout: default
title: Writing
permalink: /blog/
---

<p align="center">
  <a href="{{ '/' | relative_url }}">Home</a> |
  <a href="{{ '/' | relative_url }}#papers">Selected Papers</a> |
  <a href="{{ '/' | relative_url }}#mentoring">Mentoring</a> |
  <a href="{{ '/' | relative_url }}#projects">Projects</a> |
  <span class="nav-current">Blog</span>
</p>

{% assign sorted_posts = site.posts | sort: 'date' | reverse %}
{% assign posts_by_year = sorted_posts | group_by_exp: "post", "post.date | date: '%Y'" %}
<article class="post-article blog-index-article">
{% if posts_by_year and posts_by_year != empty %}
  <ul class="blog-archive">
    {% for post in sorted_posts %}
    <li class="blog-archive-item">
      <a class="blog-archive-link" href="{{ post.url | relative_url }}">
        <h2 class="blog-archive-title">{{ post.title }}</h2>
      </a>
      <p class="blog-archive-date">{{ post.date | date: "%B %d, %Y" }}</p>
      {% assign preview = post.excerpt | strip_html | strip %}
      {% if preview != "" %}
      <p class="blog-archive-excerpt">{{ preview | truncate: 190 }}</p>
      {% endif %}
    </li>
    {% endfor %}
  </ul>
{% else %}
  <div class="blog-empty">
    <p>No posts yet — check back soon!</p>
    <p>
      To add one, create a Markdown file in the <code>_posts</code> directory named like
      <code>YYYY-MM-DD-title.md</code> with front matter:
    </p>
    <pre><code>---
layout: post
title: "My First Post"
---</code></pre>
  </div>
{% endif %}
</article>
