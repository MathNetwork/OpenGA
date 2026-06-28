import Link from 'next/link'
import ParticleBackground from '@/components/ParticleBackground'
import { Navbar } from '@/components/Navbar'

// Projects live outside the web app, each as its own folder under a shared root.
// NEXT_PUBLIC_PROJECT_PATH points at one project; its parent is the projects root.
const PROJECT_PATH =
  process.env.NEXT_PUBLIC_PROJECT_PATH || '/Users/moqian/OpenGALib/projects/riemannian-geometry'
const PROJECTS_ROOT = PROJECT_PATH.replace(/\/[^/]+$/, '')

const PROJECTS = [
  {
    slug: 'riemannian-geometry',
    title: 'Riemannian Geometry Challenge',
    blurb:
      'A public, open initiative to build Riemannian geometry into a living, machine-verified ' +
      'textbook — a shared foundation anyone can learn from, contribute to, reuse, and build on. ' +
      'Made for everyone.',
  },
  {
    slug: 'poincare-conjecture',
    title: 'Poincaré Conjecture Challenge',
    blurb:
      'A public, open effort to build the Poincaré Conjecture — and the geometry and topology ' +
      'behind it — into a living, machine-verified textbook. Just getting started.',
  },
]

export default function Home() {
  return (
    <div className="h-full flex flex-col bg-[#0a0a0f] text-white">
      <Navbar />
      <main className="flex-1 relative overflow-y-auto">
        <ParticleBackground particleCount={260} mouseRadius={250} />
        <div className="relative z-10 max-w-3xl mx-auto px-8 py-24">
          <h2 className="text-xs uppercase tracking-wider text-white/30 mb-6">Current activity</h2>
          <div className="space-y-10">
            {PROJECTS.map((p) => (
              <div key={p.slug}>
                <Link
                  href={`/local/edit?path=${encodeURIComponent(`${PROJECTS_ROOT}/${p.slug}`)}`}
                  className="group inline-flex items-center gap-3 text-2xl font-medium text-white/85 hover:text-white transition-colors"
                >
                  {p.title}
                  <span className="text-white/25 group-hover:text-white/70 group-hover:translate-x-1 transition-all duration-200">→</span>
                </Link>
                <p className="text-sm text-white/40 mt-3 max-w-2xl">{p.blurb}</p>
              </div>
            ))}
          </div>
        </div>
      </main>
    </div>
  )
}
