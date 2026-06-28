import Link from 'next/link'
import ParticleBackground from '@/components/ParticleBackground'
import { Navbar } from '@/components/Navbar'

// The active project lives outside the web app, as its own folder.
// Override with NEXT_PUBLIC_PROJECT_PATH when deploying elsewhere.
const PROJECT_PATH =
  process.env.NEXT_PUBLIC_PROJECT_PATH || '/Users/moqian/OpenGALib/projects/riemannian-geometry'

export default function Home() {
  return (
    <div className="h-full flex flex-col bg-[#0a0a0f] text-white">
      <Navbar />
      <main className="flex-1 relative overflow-y-auto">
        <ParticleBackground particleCount={300} mouseRadius={400} />
        <div className="relative z-10 max-w-3xl mx-auto px-8 py-24">
          <h2 className="text-xs uppercase tracking-wider text-white/30 mb-4">Current activity</h2>
          <Link
            href={`/local/edit?path=${encodeURIComponent(PROJECT_PATH)}`}
            className="group inline-flex items-center gap-3 text-2xl font-medium text-white/85 hover:text-white transition-colors"
          >
            Riemannian Geometry Challenge
            <span className="text-white/25 group-hover:text-white/70 group-hover:translate-x-1 transition-all duration-200">→</span>
          </Link>
          <p className="text-sm text-white/40 mt-3 max-w-2xl">
            A public, open initiative to build Riemannian geometry into a living, machine-verified
            textbook — a shared foundation anyone can learn from, contribute to, reuse, and build on.
            Made for everyone.
          </p>
        </div>
      </main>
    </div>
  )
}
